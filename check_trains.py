#!/usr/bin/env python3
"""
Surveille mes trains SNCF et envoie une notification sur l'iPhone (via ntfy)
en cas de retard, de suppression ou de correspondance menacée.

Données : flux ouverts de la SNCF publiés sur transport.data.gouv.fr
(aucune clé, aucune inscription) :
  - horaires théoriques (GTFS), téléchargés une fois par jour
  - temps réel (GTFS-RT) : retards, suppressions, messages d'alerte

Variables d'environnement :
  NTFY_TOPIC  nom du sujet ntfy auquel l'iPhone est abonné
  TEST=1      ignore les horaires et envoie toujours un résumé (pour tester)
"""
import csv
import io
import json
import os
import sys
import unicodedata
import urllib.request
import zipfile
from datetime import date, datetime, time, timedelta
from zoneinfo import ZoneInfo

# --------------------------------------------------------------------------
# CONFIGURATION — c'est ici qu'on modifie ses horaires
# --------------------------------------------------------------------------
TRAJETS = {
    "Aller": {
        "jours": [0, 1, 2, 3, 4],  # 0 = lundi ... 4 = vendredi
        "etapes": [
            {"depart": "Orry-la-Ville", "arrivee": "Creil", "heure": "07:40"},
            {"depart": "Creil", "arrivee": "Compiègne", "heure": "08:04"},
        ],
    },
    "Retour": {
        "jours": [0, 1, 2, 3, 4],
        "etapes": [
            {"depart": "Compiègne", "arrivee": "Orry-la-Ville", "heure": "17:11"},
        ],
    },
}

SURVEILLANCE_AVANT_MIN = 60   # on commence à surveiller 1 h avant le 1er train
SEUIL_RETARD_MIN = 3          # en dessous, on considère le train à l'heure
SEUIL_CHANGEMENT_MIN = 1      # nouvelle alerte dès que l'heure de départ bouge d'au moins 1 min
ALTERNATIVES = True           # en cas de problème, cherche un trajet plus rapide
GAIN_MIN_ALTERNATIVE = 3      # … proposé seulement s'il fait arriver au moins 3 min plus tôt
PROLONGATION_MAX_MIN = 120    # si retard, on surveille jusqu'au départ réel (au plus 2 h de plus)
MARGE_CORRESPONDANCE_MIN = 2  # temps minimum pour changer de quai à Creil
CONFIRMER_A_L_HEURE = True    # période d'essai : notifie aussi quand tout est à l'heure (False pour arrêter)
CONFIRMATION_AVANT_MIN = 30   # … une fois par trajet, 30 min avant le départ
# --------------------------------------------------------------------------

GTFS_URL = "https://eu.ftp.opendatasoft.com/sncf/plandata/Export_OpenData_SNCF_GTFS_NewTripId.zip"
RT_TRIPS_URL = "https://proxy.transport.data.gouv.fr/resource/sncf-gtfs-rt-trip-updates"
RT_ALERTS_URL = "https://proxy.transport.data.gouv.fr/resource/sncf-gtfs-rt-service-alerts"

TZ = ZoneInfo("Europe/Paris")
STATE_FILE = os.environ.get("STATE_FILE", "state.json")
TEST = os.environ.get("TEST") == "1"


# ---------- outils ----------
import builtins
JOURNAL = []
_print = builtins.print


def print(*a, **k):
    JOURNAL.append(" ".join(str(x) for x in a))
    _print(*a, **k)


def publier_journal():
    if os.environ.get("GITHUB_ACTIONS") and JOURNAL:
        txt = "%0A".join(l.replace("%", "%25").replace("\n", "%0A") for l in JOURNAL)
        _print(f"::notice title=Journal::{txt}")


def norm(s):
    s = unicodedata.normalize("NFD", (s or "").lower())
    s = "".join(c for c in s if unicodedata.category(c) != "Mn")
    return "".join(c if c.isalnum() else " " for c in s).split()


def meme_nom(nom_gare, recherche):
    """« Orry-la-Ville » correspond à « Orry-la-Ville-Coye », mais « Creil » pas à « Creil Sud »… sauf si rien d'autre."""
    a, b = norm(nom_gare), norm(recherche)
    return a[:len(b)] == b


def telecharger(url, timeout=120):
    req = urllib.request.Request(url, headers={"User-Agent": "alertes-trains/1.0"})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return r.read()


def heure(jour, hh_mm):
    h, m = map(int, hh_mm.split(":"))
    return datetime.combine(jour, time(h, m), TZ)


def gtfs_heure(jour, s):
    """Heure GTFS (peut dépasser 24:00) → datetime."""
    h, m, sec = map(int, s.split(":"))
    return datetime.combine(jour, time(0), TZ) + timedelta(hours=h, minutes=m, seconds=sec)


def hhmm(d):
    return d.strftime("%H:%M")


def court(nom):
    return nom.split(" - ")[0]


# ---------- état (mémoire entre deux exécutions) ----------
def charger_etat():
    try:
        with open(STATE_FILE) as f:
            return json.load(f)
    except (OSError, ValueError):
        return {}


def sauver_etat(state):
    with open(STATE_FILE, "w") as f:
        json.dump(state, f, ensure_ascii=False, indent=1)


# ---------- horaires théoriques ----------
def lire_csv(z, nom):
    with z.open(nom) as f:
        yield from csv.DictReader(io.TextIOWrapper(f, encoding="utf-8-sig"))


def construire_plan(jour, zip_bytes):
    """Trouve, dans le GTFS, le train correspondant à chaque étape configurée pour ce jour."""
    z = zipfile.ZipFile(io.BytesIO(zip_bytes))
    noms_fichiers = set(z.namelist())

    # 1) gares
    recherches = {e[k] for t in TRAJETS.values() for e in t["etapes"] for k in ("depart", "arrivee")}
    gares = {r: {} for r in recherches}  # recherche -> {stop_id: nom}
    noms_arrets = {}
    for s in lire_csv(z, "stops.txt"):
        noms_arrets[s["stop_id"]] = s["stop_name"]
        for r in recherches:
            if meme_nom(s["stop_name"], r):
                gares[r][s["stop_id"]] = s["stop_name"]
    for r, ids in gares.items():
        noms = sorted(set(ids.values()))
        print(f"Gare « {r} » → {', '.join(noms) or 'INTROUVABLE'}")

    # 2) services circulant ce jour-là
    services = set()
    ymd, jour_sem = jour.strftime("%Y%m%d"), jour.weekday()
    cols = ["monday", "tuesday", "wednesday", "thursday", "friday", "saturday", "sunday"]
    if "calendar.txt" in noms_fichiers:
        for c in lire_csv(z, "calendar.txt"):
            if c["start_date"] <= ymd <= c["end_date"] and c[cols[jour_sem]] == "1":
                services.add(c["service_id"])
    if "calendar_dates.txt" in noms_fichiers:
        for c in lire_csv(z, "calendar_dates.txt"):
            if c["date"] == ymd:
                (services.add if c["exception_type"] == "1" else services.discard)(c["service_id"])

    trips = {}
    for t in lire_csv(z, "trips.txt"):
        if t["service_id"] in services:
            trips[t["trip_id"]] = t

    # 3) passages aux gares qui nous intéressent
    tous_ids = {sid for ids in gares.values() for sid in ids}
    passages = {}  # trip_id -> liste de (sequence, stop_id, arrivee, depart)
    terminus = {}  # trip_id -> (sequence, stop_id) du dernier arrêt
    for st in lire_csv(z, "stop_times.txt"):
        if st["trip_id"] in trips:
            q = int(st["stop_sequence"])
            if q > terminus.get(st["trip_id"], (-1, ""))[0]:
                terminus[st["trip_id"]] = (q, st["stop_id"])
        if st["stop_id"] in tous_ids and st["trip_id"] in trips:
            passages.setdefault(st["trip_id"], []).append(
                (int(st["stop_sequence"]), st["stop_id"], st["arrival_time"], st["departure_time"]))

    # 4) pour chaque étape, le train qui part à la bonne heure et dessert l'arrivée ensuite
    plan = {}
    for nom, trajet in TRAJETS.items():
        for i, e in enumerate(trajet["etapes"]):
            cle = f"{nom}:{i}"
            o_ids, d_ids = gares[e["depart"]], gares[e["arrivee"]]
            trouve = None
            for trip_id, ps in passages.items():
                ps.sort()
                for po in ps:
                    if po[1] in o_ids and po[3][:5].zfill(5) == e["heure"].zfill(5):
                        pd = next((p for p in ps if p[0] > po[0] and p[1] in d_ids), None)
                        if pd:
                            t = trips[trip_id]
                            trouve = {
                                "trip_id": trip_id,
                                "numero": t.get("trip_headsign") or t.get("trip_short_name") or "",
                                "depart_stop": po[1], "depart_seq": po[0], "depart": po[3],
                                "arrivee_stop": pd[1], "arrivee_seq": pd[0], "arrivee": pd[2],
                                "gare_depart": court(o_ids[po[1]]), "gare_arrivee": court(d_ids[pd[1]]),
                            }
                            break
                if trouve:
                    break
            plan[cle] = trouve
            print(f"{nom} {e['heure']} {e['depart']} → {e['arrivee']} : "
                  + (f"train {trouve['numero']} ({trouve['trip_id']})" if trouve else "NON TROUVÉ"))

    # 5) tous les trains du jour qui desservent au moins deux de nos gares (pour les alternatives)
    gare_de = {}
    for r, ids in gares.items():
        for sid in ids:
            gare_de.setdefault(sid, r)
    trains = {}
    for trip_id, ps in passages.items():
        ps.sort()
        arrets = [[seq, sid, gare_de[sid], arr, dep] for seq, sid, arr, dep in ps]
        if len({a[2] for a in arrets}) >= 2:
            t = trips[trip_id]
            trains[trip_id] = {"numero": t.get("trip_headsign") or t.get("trip_short_name") or "",
                               "arrets": arrets,
                               "terminus": court(noms_arrets.get(terminus.get(trip_id, (0, ""))[1], ""))}
    print(f"{len(trains)} trains du jour desservent ces gares")
    return plan, trains


def obtenir_plan(jour, state):
    if state.get("plan", {}).get("jour") == jour.isoformat() and \
            state["plan"].get("config") == TRAJETS and state["plan"].get("version") == 3:
        return state["plan"]["etapes"], state["plan"]["trains"]
    print("Téléchargement des horaires SNCF du jour…")
    etapes, trains = construire_plan(jour, telecharger(GTFS_URL, timeout=300))
    state["plan"] = {"jour": jour.isoformat(), "config": TRAJETS, "etapes": etapes, "trains": trains,
                     "version": 3}
    return etapes, trains


# ---------- temps réel ----------
def charger_temps_reel():
    from google.transit import gtfs_realtime_pb2

    maj = {}
    feed = gtfs_realtime_pb2.FeedMessage()
    feed.ParseFromString(telecharger(RT_TRIPS_URL, timeout=60))
    for ent in feed.entity:
        if ent.HasField("trip_update"):
            maj[ent.trip_update.trip.trip_id] = ent.trip_update

    alertes = {}
    try:
        feed = gtfs_realtime_pb2.FeedMessage()
        feed.ParseFromString(telecharger(RT_ALERTS_URL, timeout=60))
        for ent in feed.entity:
            if not ent.HasField("alert"):
                continue
            a = ent.alert
            txt = ""
            for champ in (a.header_text, a.description_text):
                for tr in champ.translation:
                    if tr.text and (not tr.language or tr.language.startswith("fr")):
                        txt = (txt + " — " if txt else "") + tr.text.strip()
                        break
            for ie in a.informed_entity:
                if ie.trip.trip_id and txt:
                    alertes.setdefault(ie.trip.trip_id, txt[:220])
    except Exception as ex:
        print("Alertes indisponibles :", repr(ex))
    return maj, alertes


def stu_pour(tu, stop_id, seq):
    for s in tu.stop_time_update:
        if (s.stop_id and s.stop_id == stop_id) or (s.HasField("stop_sequence") and s.stop_sequence == seq):
            return s
    return None


def heure_reelle(prevue, ev):
    """ev : StopTimeEvent GTFS-RT (time absolu ou delay)."""
    if ev is None:
        return prevue
    if ev.time:
        return datetime.fromtimestamp(ev.time, TZ)
    if ev.HasField("delay"):
        return prevue + timedelta(seconds=ev.delay)
    return prevue


def analyser_etape(e, info, jour, maj, alertes):
    from google.transit import gtfs_realtime_pb2
    SR_TRIP = gtfs_realtime_pb2.TripDescriptor
    SR_STOP = gtfs_realtime_pb2.TripUpdate.StopTimeUpdate

    r = {"libelle": f"{e['heure']} {e['depart']} → {e['arrivee']}", "gare_arrivee": e["arrivee"],
         "retard": 0, "message": ""}
    if not info:
        r["etat"] = "non_suivi"
        return r

    r["numero"] = info["numero"]
    r["gare_arrivee"] = info["gare_arrivee"]
    dep_prevu = gtfs_heure(jour, info["depart"])
    arr_prevue = gtfs_heure(jour, info["arrivee"])
    r["message"] = alertes.get(info["trip_id"], "")

    tu = maj.get(info["trip_id"])
    if tu is None:  # pas de mise à jour temps réel = circule comme prévu
        r.update(etat="ok", depart_reel=dep_prevu, arrivee_estimee=arr_prevue)
        return r

    if tu.trip.schedule_relationship == SR_TRIP.CANCELED:
        r["etat"] = "supprime"
        return r

    so = stu_pour(tu, info["depart_stop"], info["depart_seq"])
    sd = stu_pour(tu, info["arrivee_stop"], info["arrivee_seq"])
    if so is not None and so.schedule_relationship == SR_STOP.SKIPPED:
        r["etat"] = "supprime"
        return r

    dep_reel = heure_reelle(dep_prevu, so.departure if so is not None and so.HasField("departure") else
                            (so.arrival if so is not None and so.HasField("arrival") else None))
    # Si la gare de départ n'est pas listée, on prend le dernier retard connu avant elle
    if so is None:
        avant = [s for s in tu.stop_time_update if s.HasField("stop_sequence") and s.stop_sequence < info["depart_seq"]]
        if avant:
            ev = avant[-1].departure if avant[-1].HasField("departure") else avant[-1].arrival
            if ev.HasField("delay"):
                dep_reel = dep_prevu + timedelta(seconds=ev.delay)

    retard = max(0, round((dep_reel - dep_prevu).total_seconds() / 60))
    if sd is not None and sd.HasField("arrival"):
        arr_est = heure_reelle(arr_prevue, sd.arrival)
    else:
        arr_est = arr_prevue + timedelta(minutes=retard)

    r.update(retard=retard, depart_reel=dep_reel, arrivee_estimee=arr_est)
    if sd is not None and sd.schedule_relationship == SR_STOP.SKIPPED:
        r["etat"] = "modifie"
    elif retard >= SEUIL_RETARD_MIN:
        r["etat"] = "retard"
    else:
        r["etat"] = "ok"
    return r


# ---------- alternatives ----------
def temps_reel_arret(tu, arret, jour, quoi):
    """Heure réelle de passage (quoi = 'arr' ou 'dep') ; None si l'arrêt est supprimé."""
    from google.transit import gtfs_realtime_pb2
    SKIPPED = gtfs_realtime_pb2.TripUpdate.StopTimeUpdate.SKIPPED
    seq, sid, _, arr, dep = arret
    prevue = gtfs_heure(jour, arr if quoi == "arr" else dep)
    if tu is None:
        return prevue
    s = stu_pour(tu, sid, seq)
    if s is not None:
        if s.schedule_relationship == SKIPPED:
            return None
        champs = ("arrival", "departure") if quoi == "arr" else ("departure", "arrival")
        for c in champs:
            if s.HasField(c):
                return heure_reelle(prevue, getattr(s, c))
        return prevue
    # arrêt non listé : on reprend le dernier retard connu avant lui
    avant = [x for x in tu.stop_time_update if x.HasField("stop_sequence") and x.stop_sequence < seq]
    if avant:
        x = avant[-1]
        ev = x.departure if x.HasField("departure") else x.arrival
        if ev.HasField("delay"):
            return prevue + timedelta(seconds=ev.delay)
    return prevue


def troncons(trains, maj, jour, de, vers, apres):
    """Tous les trains réels de « de » vers « vers » partant à partir de « apres »."""
    from google.transit import gtfs_realtime_pb2
    CANCELED = gtfs_realtime_pb2.TripDescriptor.CANCELED
    out = []
    for trip_id, t in trains.items():
        tu = maj.get(trip_id)
        if tu is not None and tu.trip.schedule_relationship == CANCELED:
            continue
        a = t["arrets"]
        for i, ao in enumerate(a):
            if ao[2] != de:
                continue
            ad = next((x for x in a[i + 1:] if x[2] == vers), None)
            if not ad:
                continue
            dep = temps_reel_arret(tu, ao, jour, "dep")
            arr = temps_reel_arret(tu, ad, jour, "arr")
            if dep and arr and dep >= apres:
                out.append({"trip_id": trip_id, "numero": t["numero"], "de": de, "vers": vers,
                            "dep": dep, "arr": arr, "dep_prevu": gtfs_heure(jour, ao[4])})
            break
    return out


def meilleur_trajet(trains, maj, jour, de, vers, apres, gares_possibles):
    """Arrivée la plus tôt : direct ou avec un changement dans une de nos gares."""
    marge = timedelta(minutes=MARGE_CORRESPONDANCE_MIN)
    options = [[t] for t in troncons(trains, maj, jour, de, vers, apres)]
    for x in gares_possibles:
        if x in (de, vers):
            continue
        seconds = troncons(trains, maj, jour, x, vers, apres)
        for t1 in troncons(trains, maj, jour, de, x, apres):
            t2s = [t2 for t2 in seconds if t2["dep"] >= t1["arr"] + marge and t2["trip_id"] != t1["trip_id"]]
            if t2s:
                options.append([t1, min(t2s, key=lambda t: t["arr"])])
    if not options:
        return None
    # arrivée la plus tôt, puis départ le plus tard (moins d'attente), puis moins de changements
    return min(options, key=lambda o: (o[-1]["arr"], -o[0]["dep"].timestamp(), len(o)))


def chercher_alternative(nom, resultats, plan, trains, maj, jour, now):
    """Renvoie (texte, identifiant) si un trajet meilleur que le prévu existe, sinon (texte|None, None)."""
    etapes = TRAJETS[nom]["etapes"]
    if any(r["etat"] == "non_suivi" for r in resultats):
        return None, None
    marge = timedelta(minutes=MARGE_CORRESPONDANCE_MIN)

    # où en est-on ? (gare où l'on se trouve et heure à partir de laquelle on peut repartir)
    k, position, dispo = 0, etapes[0]["depart"], now
    for i, r in enumerate(resultats):
        parti = r["etat"] in ("ok", "retard") and r["depart_reel"] <= now
        if not parti:
            break
        k = i + 1
        position = etapes[i]["arrivee"]
        dispo = max(now, r["arrivee_estimee"] + marge)
    if k >= len(etapes):
        return None, None
    destination = etapes[-1]["arrivee"]

    # arrivée prévue avec le trajet actuel (None s'il ne marche plus)
    reste = resultats[k:]
    casse = any(r["etat"] in ("supprime", "modifie") for r in reste)
    for a, b in zip(reste, reste[1:]):
        if a["etat"] in ("ok", "retard") and b["etat"] in ("ok", "retard") \
                and a["arrivee_estimee"] + marge > b["depart_reel"]:
            casse = True
    if k > 0 and reste[0]["etat"] in ("ok", "retard") and reste[0]["depart_reel"] < dispo:
        casse = True
    arrivee_prevue = None if casse else reste[-1]["arrivee_estimee"]

    gares_possibles = {e["depart"] for e in etapes} | {e["arrivee"] for e in etapes}
    best = meilleur_trajet(trains, maj, jour, position, destination, dispo, gares_possibles)
    actuels = {plan.get(f"{nom}:{i}", {}).get("trip_id") for i in range(k, len(etapes)) if plan.get(f"{nom}:{i}")}

    if best is None:
        return ("🚫 Aucune autre solution en train trouvée" if casse else None), None
    if {t["trip_id"] for t in best} <= actuels:
        return None, None
    if arrivee_prevue and best[-1]["arr"] > arrivee_prevue - timedelta(minutes=GAIN_MIN_ALTERNATIVE):
        return None, None

    lignes = []
    for i, t in enumerate(best):
        retard = round((t["dep"] - t["dep_prevu"]).total_seconds() / 60)
        r_txt = f" (+{retard} min)" if retard >= 1 else ""
        verbe = "Prends" if i == 0 else "puis"
        lignes.append(f"{verbe} le {hhmm(t['dep'])}{r_txt} {t['de']} → {t['vers']} (train {t['numero']})")
    gain = ""
    if arrivee_prevue:
        gain = f", {round((arrivee_prevue - best[-1]['arr']).total_seconds() / 60)} min plus tôt"
    titre = "💡 Plus rapide" if arrivee_prevue else "💡 Solution"
    texte = f"{titre} : " + ", ".join(lignes) + f". Arrivée {hhmm(best[-1]['arr'])} à {destination}{gain}."
    return texte, "+".join(t["trip_id"] for t in best)


# ---------- message ----------
def ligne(r):
    num = f" (train {r['numero']})" if r.get("numero") else ""
    e = r["etat"]
    if e == "ok":
        txt = f"✅ {r['libelle']} : à l'heure{num}"
    elif e == "retard":
        txt = f"⚠️ {r['libelle']} : +{r['retard']} min, départ {hhmm(r['depart_reel'])}{num}"
    elif e == "supprime":
        txt = f"❌ {r['libelle']} : SUPPRIMÉ{num}"
    elif e == "modifie":
        txt = f"⚠️ {r['libelle']} : ne s'arrête plus à {r['gare_arrivee']}{num}"
    else:
        return f"❓ {r['libelle']} : absent des données SNCF du jour (non surveillé)"
    if r["message"] and e != "ok":
        txt += f"\n   ↳ {r['message']}"
    return txt


def correspondances(resultats):
    out = []
    for a, b in zip(resultats, resultats[1:]):
        menacee = (a["etat"] in ("ok", "retard") and b["etat"] in ("ok", "retard")
                   and a["arrivee_estimee"] + timedelta(minutes=MARGE_CORRESPONDANCE_MIN) > b["depart_reel"])
        out.append({"menacee": menacee,
                    "texte": (f"🔁 Correspondance à {a['gare_arrivee']} menacée : arrivée estimée "
                              f"{hhmm(a['arrivee_estimee'])}, départ {hhmm(b['depart_reel'])}")
                    if menacee else ""})
    return out


def signature(resultats, corresp, suggestion=None):
    return {"etapes": [{"etat": r["etat"], "retard": r["retard"]} for r in resultats],
            "corresp": [c["menacee"] for c in corresp], "suggestion": suggestion}


def changement_significatif(avant, apres):
    if avant is None:
        avant = {"etapes": [{"etat": "ok", "retard": 0}] * len(apres["etapes"]),
                 "corresp": [False] * len(apres["corresp"])}
    if avant["corresp"] != apres["corresp"]:
        return True
    if apres.get("suggestion") and avant.get("suggestion") != apres.get("suggestion"):
        return True
    for a, b in zip(avant["etapes"], apres["etapes"]):
        ea = "ok" if a["etat"] == "non_suivi" else a["etat"]
        eb = "ok" if b["etat"] == "non_suivi" else b["etat"]
        if ea != eb:
            return True
        if eb == "retard" and abs(a["retard"] - b["retard"]) >= SEUIL_CHANGEMENT_MIN:
            return True
    return False


def notifier(titre, texte, priorite, tags):
    body = json.dumps({"topic": os.environ["NTFY_TOPIC"], "title": titre, "message": texte,
                       "priority": priorite, "tags": tags}).encode()
    req = urllib.request.Request(os.environ.get("NTFY_SERVER", "https://ntfy.sh"), data=body,
                                 headers={"Content-Type": "application/json"})
    urllib.request.urlopen(req, timeout=20).read()
    print("Notification envoyée :", titre)


# ---------- tableau des départs (à la demande) ----------
def tableau_departs(spec, now):
    """spec = "Compiègne>Creil,Orry-la-Ville" : départs du jour de la 1re gare desservant les suivantes."""
    from google.transit import gtfs_realtime_pb2
    CANCELED = gtfs_realtime_pb2.TripDescriptor.CANCELED
    de, vers = spec.split(">", 1)
    vers = [v.strip() for v in vers.split(",") if v.strip()]
    jour = now.date()
    state = charger_etat()
    _, trains = obtenir_plan(jour, state)
    sauver_etat(state)
    maj, _ = charger_temps_reel()
    lignes = []
    for trip_id, t in trains.items():
        a = t["arrets"]
        io_ = next((i for i, x in enumerate(a) if x[2] == de.strip()), None)
        if io_ is None:
            continue
        suite = [x for x in a[io_ + 1:] if x[2] in vers]
        if not suite:
            continue
        tu = maj.get(trip_id)
        prevu = gtfs_heure(jour, a[io_][4])
        if tu is not None and tu.trip.schedule_relationship == CANCELED:
            etat, reel = "❌ supprimé", None
        else:
            reel = temps_reel_arret(tu, a[io_], jour, "dep")
            if reel is None:
                etat = "❌ ne s'arrête pas"
            else:
                r = round((reel - prevu).total_seconds() / 60)
                etat = f"⚠️ +{r} min" if r >= 1 else "✅ à l'heure"
        arrivees = []
        for x in suite:
            h = temps_reel_arret(tu, x, jour, "arr") if etat.startswith(("✅", "⚠️")) else None
            arrivees.append(f"{x[2]} {hhmm(h or gtfs_heure(jour, x[3]))}")
        term = t.get("terminus") or "?"
        lignes.append((prevu, f"{hhmm(prevu)} train {t['numero']} → terminus {term} — {etat} — passe à "
                       + ", ".join(arrivees)))
    lignes.sort()
    print(f"Départs de {de} vers {', '.join(vers)} (aujourd'hui, {len(lignes)} trains) :")
    for _, l in lignes:
        print(l)


# ---------- programme principal ----------
def main():
    now = datetime.now(TZ)
    jour = now.date()
    state = charger_etat()
    notifs = state.setdefault("notifie", {})
    for k in [k for k in notifs if not k.startswith(jour.isoformat())]:
        del notifs[k]

    a_surveiller = []
    for nom, trajet in TRAJETS.items():
        etapes = trajet["etapes"]
        debut = heure(jour, etapes[0]["heure"]) - timedelta(minutes=SURVEILLANCE_AVANT_MIN)
        fin = heure(jour, etapes[-1]["heure"]) + timedelta(minutes=2)
        prolong = state.get("prolongation", {}).get(f"{jour.isoformat()}:{nom}")
        if prolong:  # train en retard : on surveille jusqu'à son départ réel
            fin = max(fin, min(datetime.fromisoformat(prolong),
                               fin + timedelta(minutes=PROLONGATION_MAX_MIN)))
        if TEST or (now.weekday() in trajet["jours"] and debut <= now <= fin):
            a_surveiller.append(nom)
        else:
            print(f"{nom} : hors de la fenêtre de surveillance ({hhmm(debut)}–{hhmm(fin)})")
    if not a_surveiller:
        sauver_etat(state)
        return

    plan, trains = obtenir_plan(jour, state)
    maj, alertes = charger_temps_reel()
    print(f"Temps réel : {len(maj)} trains avec mise à jour, {len(alertes)} alertes")

    for nom in a_surveiller:
        etapes = TRAJETS[nom]["etapes"]
        resultats = [analyser_etape(e, plan.get(f"{nom}:{i}"), jour, maj, alertes)
                     for i, e in enumerate(etapes)]
        corresp = correspondances(resultats)
        texte = "\n".join([ligne(r) for r in resultats] + [c["texte"] for c in corresp if c["texte"]])
        suggestion = None
        probleme = any(r["etat"] in ("retard", "supprime", "modifie") for r in resultats) \
            or any(c["menacee"] for c in corresp)
        if ALTERNATIVES and probleme:
            try:
                txt_alt, suggestion = chercher_alternative(nom, resultats, plan, trains, maj, jour, now)
                if txt_alt:
                    texte += "\n" + txt_alt
            except Exception as ex:
                print("Recherche d'alternative impossible :", repr(ex))
        print(texte)

        # Prolongation de la surveillance si un train part plus tard que prévu
        prolongations = state.setdefault("prolongation", {})
        for k in [k for k in prolongations if not k.startswith(jour.isoformat())]:
            del prolongations[k]
        departs = [r["depart_reel"] + timedelta(minutes=2) for r in resultats
                   if r["etat"] in ("retard", "ok") and r.get("depart_reel")]
        cle_p = f"{jour.isoformat()}:{nom}"
        if any(r["etat"] == "retard" for r in resultats) and departs:
            prolongations[cle_p] = max(departs).isoformat()
        else:
            prolongations.pop(cle_p, None)

        if TEST:
            notifier(f"🧪 Test – {nom}", texte, 3, ["train"])
            continue

        cle = f"{jour.isoformat()}:{nom}"
        sig = signature(resultats, corresp, suggestion)
        if not changement_significatif(notifs.get(cle), sig):
            depart = heure(jour, etapes[0]["heure"])
            if (CONFIRMER_A_L_HEURE and cle not in notifs and cle + ":ok" not in notifs
                    and now >= depart - timedelta(minutes=CONFIRMATION_AVANT_MIN)):
                notifier(f"🚆 {nom} : tout est à l'heure", texte, 3, ["white_check_mark", "train"])
                notifs[cle + ":ok"] = True
            else:
                print("Rien de nouveau depuis la dernière notification.")
            continue

        if suggestion:
            quoi, prio = "change de train", 5
        elif any(r["etat"] == "supprime" for r in resultats):
            quoi, prio = "train supprimé", 5
        elif any(r["etat"] == "modifie" for r in resultats):
            quoi, prio = "train modifié", 5
        elif any(c["menacee"] for c in corresp):
            quoi, prio = "correspondance menacée", 5
        elif any(r["etat"] == "retard" for r in resultats):
            quoi, prio = "retard", 4
        else:
            quoi, prio = None, 3

        if quoi:
            notifier(f"🚆 {nom} : {quoi}", texte, prio, ["warning", "train"])
        elif now >= heure(jour, etapes[-1]["heure"]):
            # le train vient sans doute de partir (il disparaît du temps réel) : pas de faux « retour à la normale »
            print("Train parti, pas de notification.")
            continue
        else:
            notifier(f"🚆 {nom} : retour à la normale", texte, prio, ["white_check_mark", "train"])
        notifs[cle] = sig

    sauver_etat(state)


if __name__ == "__main__":
    try:
        if os.environ.get("DEPARTS"):
            tableau_departs(os.environ["DEPARTS"], datetime.now(TZ))
        else:
            main()
    except Exception as e:
        print("Erreur :", repr(e), file=sys.stderr)
        publier_journal()
        sys.exit(1)
    publier_journal()
