#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
AstroLogbuch – lokaler Ordner-Scanner
================================================

Was das Programm macht:
  Es liest einen Astro-Ordner ein, ermittelt pro Projekt-Unterordner
  Nächte, Belichtungszeiten, Filter und einen Bearbeitungsstatus nach
  festen Regeln, und zeigt das Ergebnis als Dashboard in einem eigenen
  Programmfenster an (kein Browser nötig, siehe nächster Absatz).

  Es liest nur (keine Datei wird verändert oder gelöscht).

Bedienung:
  1. AstroLogbuch.exe per Doppelklick starten.
  2. Beim allerersten Start (oder wenn noch kein Ordner gewählt wurde)
     fragt das Programm nach dem Astro-Ordner. Diese Wahl bleibt
     danach dauerhaft gespeichert (AstroLogbuch_config.json).
  3. Über das Zahnrad-Symbol oben rechts im Dashboard lassen sich der
     Ordner, der Standort (Breitengrad) sowie eigene Kamera-/Filter-
     Bezeichnungen jederzeit anpassen; "Speichern" liest den Ordner
     danach sofort neu ein.

  Ist das Zusatzpaket "pywebview" nicht installiert, fällt das
  Programm automatisch auf den (älteren) Browser-Modus zurück: Es
  öffnet dann den Standardbrowser statt eines eigenen Fensters, und
  die Einstellungen müssen von Hand in AstroLogbuch_config.json
  bearbeitet werden. Siehe ANLEITUNG.txt für die Installation von
  pywebview.

  Bei einem Fehler beim Einlesen erscheint eine Fehlerseite direkt im
  Programmfenster und zeigt die Meldung, statt sich einfach stumm zu
  schliessen. Startest du astro_dashboard.py direkt (statt der .exe),
  siehst du zusätzlich ein Konsolenfenster mit dem rohen Scan-Fortschritt.

Status-Regeln (nachvollziehbar, in dieser Reihenfolge geprüft):
  1. "done" im Ordnernamen                         -> Fertig
  2. fertige Datei (jpg/png/tif/psd/mp4) im Ordner  -> In Arbeit
     oder in einem Stack-/PI-Unterordner, aber kein "done" im Namen
  3. Monatsname im Ordnernamen (z. B. "August")     -> Geplant (<Monat>), kein Ergebnis
     gefunden - kann trotzdem Daten enthalten (z. B. Kalibrieraufnahmen)
  4. nur Rohaufnahmen (Light), kein Stack           -> Nur Rohdaten
  5. Stack vorhanden, aber keine fertige Datei       -> Unklar
  6. so gut wie keine Dateien                        -> Kaum begonnen

  "Fertig" wird ausschliesslich über das "done"-Tag im Ordnernamen
  vergeben, nie automatisch aus einer vorhandenen Bilddatei geschlossen.

Belichtungszeiten:
  - Wird aus Unterordnernamen mit einer Stundenangabe gelesen
    (z. B. "NACHT_03_15.03.2025_Ha_8.3h" -> 8.3h), das ist die
    zuverlässigste Quelle.
  - Sonst aus Light-Dateinamen im ASIAIR/NINA-Schema
    (Light_<Ziel>_<Belichtung>s_Bin<n>_<Kamera>[_Filter]_gain<g>_
    <Zeitstempel>_<Nr>.fit).
  - Wenn keines von beidem zutrifft (z. B. alte DSLR-Aufnahmen ohne
    Belichtungszeit im Namen), wird NICHT geschätzt, sondern nur die
    Anzahl Dateien angegeben. Das ist bewusst so, um keine erfundenen
    Zahlen als sicher auszugeben.

Objekt-Katalog für die Sichtbarkeitsberechnung:
  Die Koordinaten für das "optimale Beobachtungsfenster" werden in drei
  Stufen ermittelt: (1) der von Hand gepflegte OBJECT_CATALOG unten für
  Spezialfälle/deutsche Namen, (2) der eingebaute BIG_CATALOG (NGC/IC/
  Messier/Sh2/LBN, aus OpenNGC, rund 14000 Einträge, komplett offline),
  (3) bei Bedarf eine einmalige Online-Namensauflösung (Sesame/CDS) mit
  dauerhafter lokaler Zwischenspeicherung in AstroLogbuch_object_cache.json.
  Kometen sind davon ausgenommen (keine feste Position, ein Fenster wäre
  fachlich falsch). Details siehe ANLEITUNG.txt.
"""

import os
import re
import sys
import time
import json
import math
import html
import base64
import webbrowser
import traceback
import subprocess
import threading
import http.server
from io import BytesIO
from urllib.parse import urlparse, parse_qs, quote, urlencode
from urllib.request import urlopen, Request
from urllib.error import URLError, HTTPError
from datetime import date, timedelta

try:
    from PIL import Image
    # Eigene Dateien, kein Fremd-Upload: die Decompression-Bomb-Warnung
    # von Pillow (bei sehr grossen Mosaiken/Panoramen ueber ca. 89 MP)
    # ist hier nicht relevant und wird deshalb bewusst abgeschaltet.
    Image.MAX_IMAGE_PIXELS = None
    HAVE_PIL = True
except Exception:
    HAVE_PIL = False

# ======================================================================
# KONFIGURATION
# ======================================================================
# Die Werte hier unten sind nur noch die werkseitigen Vorgaben fuer einen
# ganz neuen Nutzer. Deine eigenen Einstellungen (Ordner, Standort,
# Kamera-/Filterbezeichnungen, ausgeschlossene Ordner, Online-Aufloesung
# an/aus) werden nicht mehr im Skript selbst bearbeitet, sondern über die
# Einstellungen im Programmfenster (Zahnrad-Symbol) gesetzt und dauerhaft in
# AstroLogbuch_config.json neben dem Programm gespeichert. Bearbeite die
# Konstanten hier nur noch, wenn du die werkseitigen Vorgaben fuer eine
# komplett neue Installation (noch keine config-Datei vorhanden) aendern
# willst.

DEFAULT_CONFIG = {
    "root_folder": "",   # leer = beim ersten Start wird ein Ordner abgefragt
    "latitude": 50.0,    # Breitengrad des Beobachtungsorts
    "exclude_folder_names": [
        "asiair", "speicherkartesave", "testaufnahmen", "5stern", "light", "neu",
    ],
    # Kamera-Rohcode (aus dem Dateinamen, z. B. "2600") -> sprechender Name.
    # Ohne Eintrag wird einfach der Rohcode angezeigt.
    "camera_map": {},
    # Filter-Kuerzel aus dem Dateinamen -> sprechender Name. Die Vorgabe
    # deckt die bei ASIAIR/NINA ueblichen Kuerzel ab, kann aber frei
    # ergaenzt/ueberschrieben werden (z. B. fuer andere Aufnahmesoftware).
    "filter_map": {
        "L": "Luminance", "R": "Rot", "G": "Gruen", "B": "Blau",
        "H": "Ha", "HA": "Ha", "O": "OIII", "OIII": "OIII", "S": "SII", "SII": "SII",
        "LP": "LP/Duo", "CLS": "CLS", "DUO": "Duo",
    },
    "calib_words": ["dark", "flat", "bias", "offset", "dunkel", "darkflat"],
    "show_thumbnails": True,
    "online_lookup_enabled": True,
    # Manuelle Vorschaubild-Wahl je Projekt (Klick auf das Vorschaubild in der
    # Tabelle). Schluessel = Projektordnerpfad. Wert = relativer Dateipfad
    # (manuell gewaehltes Bild) oder null (explizit "kein Bild"). Fehlt der
    # Schluessel fuer ein Projekt, gilt weiterhin die automatische Heuristik
    # (pick_preview_file()) - das ist der Normalfall fuer die meisten Projekte.
    "preview_overrides": {},
}

# "astrologbuch" (der Ordner dieses Tools selbst) ist immer ausgeschlossen,
# unabhaengig davon, was in den Einstellungen steht, damit sich das
# Programm nie selbst als Projektzeile auffuehrt.
ALWAYS_EXCLUDED_FOLDER_NAMES = {"astrologbuch"}

# Bei jeder inhaltlichen Aenderung erhoehen und einen Eintrag in
# CHANGELOG.txt ergaenzen (siehe dort). Wird im Dashboard (Kopfzeile
# rechts) angezeigt, damit erkennbar ist, welcher Stand gerade laeuft.
APP_VERSION = "1.9.0"

CONFIG_FILENAME = "AstroLogbuch_config.json"
ICON_FILENAME = "AstroLogbuch.ico"  # neben Skript/EXE, siehe Schritt 2 in ANLEITUNG.txt

# Laufzeit-Variablen, aus der Konfiguration befuellt (siehe apply_config()
# weiter unten). Die Vorgaben hier greifen nur, falls apply_config() aus
# irgendeinem Grund uebersprungen wuerde.
ROOT_FOLDER = ""
LATITUDE = DEFAULT_CONFIG["latitude"]
EXCLUDE_FOLDER_NAMES = set(DEFAULT_CONFIG["exclude_folder_names"]) | ALWAYS_EXCLUDED_FOLDER_NAMES
SHOW_THUMBNAILS = DEFAULT_CONFIG["show_thumbnails"]
PREVIEW_OVERRIDES = dict(DEFAULT_CONFIG["preview_overrides"])

# Optional: Ordner, die eigentlich zu einem anderen Projekt gehoeren
# (z. B. alte, falsch einsortierte Zwischenordner), zusammenfuehren.
# Schluessel = exakter Ordnername der Quelle, Wert = exakter Ordnername
# des Ziels. Beide muessen als Ordner existieren. Die Kennzahlen der
# Quelle werden dann in die Zielzeile eingerechnet, die Quelle selbst
# taucht nicht mehr als eigene Zeile auf. Das ist (noch) keine Einstellung
# im Programmfenster, sondern ein Sonderfall fuer Handarbeit im Skript.
MERGE_INTO = {
    # "200313_M101": "M101 - Feuerrad-Galaxie",
    # "200314_M101": "M101 - Feuerrad-Galaxie",
}

THUMBNAIL_MAX_PX = 160
# Notbremse fuer make_thumbnail(): Oeffnet/liest die Bilddatei tatsaechlich
# (nicht nur Metadaten) - genau das kann ein Echtzeit-Virenschutz am
# gruendlichsten scannen und dadurch minutenlang blockieren (siehe
# _fetch_url_with_hard_timeout weiter unten fuer dasselbe Muster bei der
# Online-Namensaufloesung; hier beobachtet als "Programm haengt sich beim
# Start auf", Fenstertitel "Keine Rueckmeldung", waehrend Phase 2 lief).
THUMBNAIL_TIMEOUT_SECONDS = 5

# Fuers Vorschaubild-Auswahlfenster (list_preview_candidates): Dateien
# oberhalb dieser Groesse bekommen dort bewusst KEINE Live-Vorschau erzeugt,
# sondern nur einen Platzhalter (Name bleibt trotzdem waehlbar). Grund:
# unbearbeitete lineare Master-TIFFs direkt aus dem Stacking koennen
# mehrere hundert MB gross sein - deren Dekodierung fuer eine reine
# Auswahl-Miniatur wuerde das Oeffnen des Fensters spuerbar verzoegern,
# obwohl die automatische Heuristik (pick_preview_file) so eine Datei wegen
# der Endungs-Prioritaet ohnehin nie waehlen wuerde.
PREVIEW_PICKER_MAX_THUMB_BYTES = 15 * 1024 * 1024

# Fuer das "optimale Fenster" wird zuerst der eingebaute Katalog probiert
# (OBJECT_CATALOG unten, dann der grosse NGC/IC/Messier-Katalog, siehe
# BIG_CATALOG). Ist ein Objekt dort nicht bekannt (z. B. eine LDN- oder
# Sharpless-Bezeichnung, oder ein rein informeller Name), fragt das
# Programm bei aktivierter Online-Aufloesung (siehe Einstellungen)
# zusaetzlich einmalig eine oeffentliche astronomische Datenbank an
# (Sesame/CDS) und speichert das Ergebnis danach dauerhaft lokal, sodass
# dafuer nur beim ersten Antreffen eines neuen/unbekannten Objekts eine
# Internetverbindung noetig ist. Ist die Online-Aufloesung abgeschaltet,
# bleibt das Tool komplett offline, unbekannte Objekte bekommen dann
# weiterhin kein Fenster.
ONLINE_LOOKUP_ENABLED = DEFAULT_CONFIG["online_lookup_enabled"]
OBJECT_CACHE_FILENAME = "AstroLogbuch_object_cache.json"
ONLINE_LOOKUP_TIMEOUT = 4  # Sekunden pro Versuch


def load_config(config_path):
    """Liest die gespeicherten Einstellungen, ergaenzt fehlende Felder aus
    DEFAULT_CONFIG (z. B. nach einem Update mit neuen Einstellungsfeldern)
    und gibt garantiert ein vollstaendiges Config-Dict zurueck. Gibt es noch
    keine Datei (erster Start / neuer Nutzer), sind das einfach die
    werkseitigen Vorgaben."""
    cfg = json.loads(json.dumps(DEFAULT_CONFIG))  # unabhaengige Kopie
    try:
        with open(config_path, "r", encoding="utf-8") as f:
            saved = json.load(f)
        if isinstance(saved, dict):
            cfg.update(saved)
    except Exception:
        pass
    return cfg


def save_config(config_path, cfg):
    try:
        with open(config_path, "w", encoding="utf-8") as f:
            json.dump(cfg, f, ensure_ascii=False, indent=2)
        return True
    except Exception:
        return False


def apply_config(cfg):
    """Uebernimmt ein Config-Dict in die zur Laufzeit tatsaechlich
    verwendeten Variablen. Wird beim Start und nach jedem Speichern der
    Einstellungen im Programmfenster aufgerufen."""
    global ROOT_FOLDER, LATITUDE, EXCLUDE_FOLDER_NAMES, CAMERA_MAP, \
        FILTER_MAP, CALIB_WORDS, SHOW_THUMBNAILS, ONLINE_LOOKUP_ENABLED, PREVIEW_OVERRIDES
    ROOT_FOLDER = str(cfg.get("root_folder") or "")
    try:
        LATITUDE = float(cfg.get("latitude", DEFAULT_CONFIG["latitude"]))
    except (TypeError, ValueError):
        LATITUDE = DEFAULT_CONFIG["latitude"]
    exclude = cfg.get("exclude_folder_names", DEFAULT_CONFIG["exclude_folder_names"])
    EXCLUDE_FOLDER_NAMES = {str(w).strip().lower() for w in exclude if str(w).strip()} \
        | ALWAYS_EXCLUDED_FOLDER_NAMES
    # Schluessel bewusst klein: resolve_camera_labels() schlaegt mit
    # model.lower() nach. Bei ASI-Kameras ist der Schluessel eine reine
    # Modellnummer ("2600"), da fiel das nie auf - bei DSLR-Bezeichnungen
    # wie "A7RIIIJ" haette ein vom Nutzer gross geschriebener Eintrag
    # sonst stillschweigend nicht gegriffen.
    CAMERA_MAP = {str(k).lower(): str(v) for k, v in cfg.get("camera_map", {}).items()}
    FILTER_MAP = {str(k).upper(): str(v) for k, v in cfg.get("filter_map", {}).items()}
    calib = cfg.get("calib_words", DEFAULT_CONFIG["calib_words"])
    CALIB_WORDS = tuple(str(w).strip().lower() for w in calib if str(w).strip())
    SHOW_THUMBNAILS = bool(cfg.get("show_thumbnails", True))
    ONLINE_LOOKUP_ENABLED = bool(cfg.get("online_lookup_enabled", True))
    overrides = cfg.get("preview_overrides", {})
    PREVIEW_OVERRIDES = dict(overrides) if isinstance(overrides, dict) else {}


# Objekt-Katalog: Namensfragment (klein geschrieben, ohne Sonderzeichen-Sorgen)
# -> (Rektaszension in Stunden, Deklination in Grad)
# Ergänze hier gern weitere Objekte. Die Zuordnung erfolgt, sobald das
# Fragment irgendwo im Ordnernamen vorkommt.
OBJECT_CATALOG = {
    "ngc 7129": (21 + 43/60, 66 + 6/60),
    "ngc7129": (21 + 43/60, 66 + 6/60),
    "sh2-140": (22 + 19/60 + 21/3600, 63 + 14/60 + 54/3600),
    "sh2140": (22 + 19/60 + 21/3600, 63 + 14/60 + 54/3600),
    "sh 2-140": (22 + 19/60 + 21/3600, 63 + 14/60 + 54/3600),
    "lbn 406": (16 + 50/60, 61 + 9/60),
    "lbn406": (16 + 50/60, 61 + 9/60),
    "laughing skull": (16 + 50/60, 61 + 9/60),
    "lbn 691": (9 + 37/60, 65 + 56/60),
    "lbn691": (9 + 37/60, 65 + 56/60),
    "ngc 5363": (13 + 56/60 + 7/3600, 5 + 15/60 + 17/3600),
    "lgg 362": (13 + 56/60 + 7/3600, 5 + 15/60 + 17/3600),
    "abell 39": (16 + 27/60 + 33/3600, 27 + 54/60),
    "california": (4 + 0/60 + 42/3600, 36 + 37/60),
    "ic 1396": (21 + 36/60 + 48/3600, 57 + 30/60),
    "ic1396": (21 + 36/60 + 48/3600, 57 + 30/60),
    "elefantenruessel": (21 + 36/60 + 48/3600, 57 + 30/60),
    "elefantenrüssel": (21 + 36/60 + 48/3600, 57 + 30/60),
    "ic 1805": (2 + 33/60 + 24/3600, 61 + 26/60),
    "ic1805": (2 + 33/60 + 24/3600, 61 + 26/60),
    "herznebel": (2 + 33/60 + 24/3600, 61 + 26/60),
    "m31": (0 + 42/60 + 44/3600, 41 + 16/60),
    "andromeda": (0 + 42/60 + 44/3600, 41 + 16/60),
    "m42": (5 + 35/60 + 17/3600, -5 - 23/60),
    "orion": (5 + 35/60 + 17/3600, -5 - 23/60),
    "m63": (13 + 15/60 + 49/3600, 42 + 1/60),
    "sunflower": (13 + 15/60 + 49/3600, 42 + 1/60),
    "m81": (9 + 55/60 + 33/3600, 69 + 3/60),
    "bodes galaxie": (9 + 55/60 + 33/3600, 69 + 3/60),
    "markarian": (12 + 27/60, 13 + 10/60),
    "markarjan": (12 + 27/60, 13 + 10/60),
    "ngc 7380": (22 + 47/60 + 20/3600, 58 + 6/60),
    "ngc7380": (22 + 47/60 + 20/3600, 58 + 6/60),
    "wizard": (22 + 47/60 + 20/3600, 58 + 6/60),
    "ngc 2264": (6 + 41/60 + 6/3600, 9 + 53/60),
    "ngc2264": (6 + 41/60 + 6/3600, 9 + 53/60),
    "cone nebula": (6 + 41/60 + 6/3600, 9 + 53/60),
    "christmas tree": (6 + 41/60 + 6/3600, 9 + 53/60),
    "ngc 869": (2 + 19/60, 57 + 9/60),
    "ngc869": (2 + 19/60, 57 + 9/60),
    "h/": (2 + 19/60, 57 + 9/60),
    "doppelsternhaufen": (2 + 19/60, 57 + 9/60),
    "m45": (3 + 47/60 + 24/3600, 24 + 7/60),
    "plejaden": (3 + 47/60 + 24/3600, 24 + 7/60),
    "m101": (14 + 3/60 + 13/3600, 54 + 21/60),
    "feuerrad": (14 + 3/60 + 13/3600, 54 + 21/60),
    "cirrusnebel": (20 + 51/60, 31.0),
    "veil nebula": (20 + 51/60, 31.0),
    "schleiernebel": (20 + 51/60, 31.0),
    "abell 1656": (12 + 59/60 + 48.7/3600, 27 + 58/60 + 50/3600),
    "abell1656": (12 + 59/60 + 48.7/3600, 27 + 58/60 + 50/3600),
    "abell_1656": (12 + 59/60 + 48.7/3600, 27 + 58/60 + 50/3600),
    "coma galaxienhaufen": (12 + 59/60 + 48.7/3600, 27 + 58/60 + 50/3600),
    "coma_galaxienhaufen": (12 + 59/60 + 48.7/3600, 27 + 58/60 + 50/3600),
    "comagalaxienhaufen": (12 + 59/60 + 48.7/3600, 27 + 58/60 + 50/3600),
    "coma cluster": (12 + 59/60 + 48.7/3600, 27 + 58/60 + 50/3600),
    "komahaufen": (12 + 59/60 + 48.7/3600, 27 + 58/60 + 50/3600),
}

# ======================================================================
# Grosser Objektkatalog (automatisch, NGC/IC/Messier/Sharpless/LBN/...)
# ======================================================================
# OBJECT_CATALOG oben ist fuer Spezialfaelle und deutsche Namen gedacht, die
# man von Hand ergaenzt. Damit aber auch neue Projekte automatisch ein
# optimales Fenster bekommen, ohne jedes Mal von Hand einen Eintrag
# hinzuzufuegen, ist hier zusaetzlich ein grosser, aus einer echten
# astronomischen Datenbank abgeleiteter Katalog eingebettet: OpenNGC
# (https://github.com/mattiaverga/OpenNGC, Autor Mattia Verga, Lizenz
# CC-BY-SA-4.0), das seinerseits Daten aus NED, HyperLeda, SIMBAD und
# HEASARC zusammenfuehrt. Abgedeckt sind alle NGC- und IC-Objekte, dazu
# Messier-Nummern und einige zusaetzliche, ueber die "Identifiers"-Spalte
# gefundene Sharpless(Sh2)- und LBN-Bezeichnungen. Das deckt praktisch alle
# ueblichen Katalogbezeichnungen ab (Stand der Daten: siehe Kommentar beim
# naechsten Update). Enthaelt das Objekt nur einen informellen Namen ohne
# Katalognummer (oder eine Bezeichnung aus einem hier nicht enthaltenen
# Katalog wie LDN), greift als naechstes die Online-Namensaufloesung weiter
# unten.
#
# Format je Zeile: kommagetrennte Schluessel (alle klein, ohne Trennzeichen)
# TAB Rektaszension-in-Stunden TAB Deklination-in-Grad. Wird einmalig beim
# Start in ein Dictionary eingelesen (siehe _load_big_catalog()).
BIG_CATALOG_BLOB = """ic1	0.140847	27.717667
ic2	0.183578	-12.822861
ic3	0.201692	-0.415222
ic4	0.22415	17.486444
ic5	0.293036	-9.543361
ic6	0.315289	-3.276083
ic7	0.314767	10.594694
ic8	0.317422	-3.222083
ic9	0.328883	-14.121889
ic10	0.33815	59.303778
ic11,lbn616,ngc281	0.883153	56.621889
ic12	0.337514	-2.653111
ic13	0.338914	7.7005
ic14	0.375358	10.49025
ic15	0.465997	-0.061278
ic16	0.468792	-13.093917
ic17	0.474939	2.648611
ic18	0.476378	-11.586694
ic19	0.477633	-11.640778
ic20	0.477689	-13.010306
ic21	0.486231	-0.163778
ic22	0.492547	-9.08075
ic23	0.514111	-12.72025
ic24	0.521286	30.839306
ic25	0.520025	-0.407361
ic26,ngc135	0.529428	-13.337472
ic27	0.551733	-13.3715
ic28	0.552422	-13.456278
ic29	0.569667	-2.177639
ic30	0.570756	-2.084583
ic31	0.573508	12.268167
ic32	0.583803	-2.141694
ic33	0.584767	-2.137694
ic34	0.59345	9.12425
ic35	0.627744	10.357972
ic36	0.630458	-15.441278
ic37	0.642828	-15.358694
ic38	0.6441	-15.419833
ic39,ngc178	0.652333	-14.172833
ic40	0.655944	2.456222
ic41	0.661214	-14.174333
ic42	0.684956	-15.428083
ic43	0.706128	29.641639
ic44,ngc223	0.704411	0.8455
ic45	0.710094	29.65525
ic46	0.716103	27.253472
ic47	0.715281	-13.740722
ic1577,ic48	0.726242	-8.1865
ic49	0.732258	1.850278
ic50	0.768253	-9.503
ic51	0.773394	-13.442361
ic52	0.806606	4.091861
ic53	0.844658	10.600278
ic54	0.846347	-2.287778
ic55	0.861775	7.718528
ic56	0.858317	-12.844306
ic57	0.913472	11.841194
ic58	0.917344	-13.678083
ic59,lbn620	0.957947	61.143667
ic60	0.934508	-13.357917
ic61	0.952	7.507083
ic62	0.978872	11.808
ic63,lbn622	0.991344	60.911694
ic64	0.990117	27.059056
ic65	1.015394	47.681972
ic66	1.009028	30.797222
ic67	1.004906	-6.91075
ic68	1.006014	-6.944111
ic69	1.023239	31.040833
ic70	1.017764	0.05075
ic71	1.022017	-6.767167
ic72	1.026308	-6.777944
ic73	1.081375	4.767139
ic74	1.098875	4.09025
ic75	1.119892	10.836889
ic76	1.136586	-4.5545
ic77	1.145486	-15.420917
ic78	1.146583	-15.845083
ic79	1.147142	-15.948583
ic80	1.147472	-15.4075
ic81	1.156183	-1.695861
ic82	1.151608	-16.000306
ic83	1.174939	1.689361
ic84	1.190444	1.640194
ic85	1.197097	-0.452472
ic86	1.224589	-16.241667
ic87	1.237719	0.765333
ic88	1.242028	0.79175
ic89,ngc446	1.267669	4.294111
ic90	1.275097	-7.977139
ic91	1.310953	2.553667
ic92,ngc468	1.330139	32.767778
ic1671,ic93	1.317317	-17.060389
ic94	1.334858	32.717333
ic95	1.321633	-12.574139
ic96	1.342561	29.61725
ic97,ngc475	1.333889	14.861056
ic98	1.348578	-12.604722
ic99	1.374267	-12.952556
ic100	1.381656	-4.643028
ic101	1.402375	9.930528
ic102	1.407314	9.886556
ic103	1.410122	2.04425
ic104	1.409333	-1.456722
ic105	1.412847	2.075278
ic106,ngc530	1.411569	-1.587083
ic107,ic1700	1.423517	14.864611
ic108	1.410822	-12.635583
ic109	1.420303	2.066222
ic110	1.429611	33.514694
ic111	1.433369	33.497111
ic112	1.434172	11.442972
ic113	1.440417	19.191972
ic114	1.439606	9.909944
ic115	1.448456	19.214694
ic116	1.447381	-4.982278
ic117,ngc560	1.457061	-1.912972
ic118	1.460011	-4.997472
ic119	1.465283	-2.040472
ic120	1.470267	-1.915528
ic121	1.472717	2.513028
ic122	1.470333	-14.838889
ic123	1.480961	2.446444
ic124	1.485856	-1.937028
ic125	1.488431	-13.279833
ic126	1.496628	-1.98375
ic127	1.496558	-6.980056
ic128	1.523297	-12.624389
ic129	1.52535	-12.654389
ic130	1.52465	-15.591611
ic131	1.55405	30.75325
ic132	1.554422	30.945611
ic133	1.554217	30.888389
ic134	1.556944	30.900667
ic135	1.570981	30.620083
ic136	1.571122	30.562056
ic137	1.560808	30.5225
ic138	1.55055	-0.689833
ic139	1.566456	30.567444
ic140	1.566158	30.550139
ic141	1.547697	-14.814611
ic142	1.565425	30.757806
ic143	1.569703	30.776417
ic144	1.628014	-13.314667
ic145	1.644022	0.7415
ic146,ngc648	1.644386	-17.831194
ic147	1.666597	-14.862639
ic148	1.707492	13.977028
ic149	1.70705	-16.300417
ic150	1.715978	4.200167
ic151	1.732631	13.202611
ic152	1.735386	13.035861
ic153	1.743392	12.628944
ic154	1.754519	10.649194
ic155	1.792314	60.610833
ic156	1.758114	10.552722
ic157	1.761778	12.873333
ic158	1.764867	-6.935694
ic159	1.773625	-8.636611
ic160	1.774878	-13.247722
ic161	1.81215	10.507889
ic162	1.814842	10.521611
ic163	1.820831	20.711306
ic164	1.819003	-3.904389
ic165,ngc684	1.837228	27.645667
ic166	1.873283	61.852611
ic167	1.852378	21.912806
ic168	1.841008	-8.522944
ic169	1.844267	-12.679611
ic170	1.865978	-8.517611
ic171	1.919503	35.281889
ic172	1.915064	0.811222
ic173	1.932542	1.285167
ic174	1.9378	3.761861
ic175	1.938572	1.332417
ic176	1.948167	-2.018972
ic177	1.950161	-0.089861
ic178	1.981908	36.674694
ic179	2.003194	38.021333
ic180	2.000114	23.604333
ic181	2.000647	23.658639
ic182	1.997725	7.411833
ic183	1.992792	-5.347139
ic184	1.997564	-6.840389
ic185	2.001678	-1.528333
ic186	2.006806	-1.551722
ic186a	2.006667	-1.552861
ic186b	2.007069	-1.549806
ic187	2.025211	26.480972
ic188	2.029583	26.546889
ic189	2.031364	23.5515
ic190	2.035356	23.549833
ic191,ngc794	2.041481	18.373
ic192	2.042331	16.014167
ic193	2.041939	11.093083
ic194	2.05145	2.61425
ic195	2.062392	14.709278
ic196	2.063833	14.739139
ic197	2.068036	2.786833
ic198	2.100867	9.295556
ic1778,ic199	2.105389	9.227417
ic200	2.090733	31.175333
ic201	2.120914	9.115056
ic202	2.124628	9.168306
ic203	2.124903	9.122639
ic204	2.124189	-1.430194
ic205	2.124286	-2.091278
ic206	2.158522	-6.968389
ic207	2.160931	-6.922194
ic208	2.141039	6.394917
ic209	2.149642	-7.058917
ic210	2.157856	-9.680333
ic211	2.185556	3.8525
ic212	2.227294	16.593944
ic213	2.234522	16.455889
ic214	2.234886	5.17325
ic215	2.235961	-6.806333
ic216	2.265422	-2.015111
ic1787,ic217	2.269567	-11.926722
ic218	2.285347	1.282333
ic219	2.310786	-6.903333
ic220	2.319925	-12.781639
ic221	2.378028	28.256972
ic222	2.379958	11.638333
ic223	2.366972	-20.745917
ic224	2.412539	-12.564472
ic225	2.441192	1.160528
ic226	2.462758	28.208833
ic227	2.467669	28.175333
ic228,ngc944	2.444869	-14.515639
ic229	2.456136	-23.813
ic230	2.479803	-10.831361
ic231	2.498997	1.179083
ic232	2.519894	1.265639
ic233	2.527972	2.809917
ic234	2.527144	-0.14025
ic235	2.547442	20.64125
ic236	2.548836	-0.13125
ic237	2.558769	1.139889
ic238	2.589633	12.837722
ic239	2.607744	38.969917
ic240	2.649603	41.719417
ic241	2.631806	2.328028
ic242	2.639981	-6.933944
ic243	2.642267	-6.902139
ic244	2.656869	2.728806
ic245	2.648511	-14.305556
ic246	2.674611	2.478639
ic247	2.669106	-11.733778
ic248	2.690508	17.812222
ic249,ngc1051,ngc961	2.684025	-6.935917
ic250	2.681742	-13.313556
ic251	2.687181	-14.957833
ic252	2.695869	-14.84825
ic253	2.701597	-15.046833
ic254	2.701383	-15.106639
ic255	2.784225	16.288028
ic256	2.827861	46.954667
ic257	2.829289	46.976194
ic258	2.829472	41.051667
ic259	2.828022	41.055111
ic260	2.850244	46.954778
ic261,ngc1120	2.817803	-14.470694
ic262	2.862019	42.828278
ic263	2.827767	-0.069861
ic264	2.813228	-0.109194
ic265	2.912217	41.655333
ic266	2.918008	42.262333
ic267	2.897292	12.849222
ic268	2.924153	-14.103
ic269	2.924025	-14.066806
ic270	2.928942	-14.207889
ic271	2.933181	-12.007861
ic272	2.935122	-14.186639
ic273	2.952994	2.775056
ic274	3.001453	44.213167
ic275	3.015917	44.348333
ic276	2.978072	-15.703111
ic277	2.997389	2.771361
ic278	3.025122	37.766
ic279	3.020058	16.209222
ic280	3.051003	42.359306
ic281,ngc1177	3.076981	42.362833
ic282,ngc1198	3.103678	41.848944
ic283	3.064017	-0.204444
ic284	3.102753	42.371917
ic285	3.068394	-12.015444
ic286	3.079783	-6.484528
ic287	3.082728	-12.070444
ic288	3.125808	42.387556
ic289	3.172017	61.316778
ic1884,ic290	3.161872	40.974222
ic291	3.124014	-12.587444
ic1887,ic292	3.170256	40.765667
ic1888,ic293	3.182267	41.137111
ic1889,ic294	3.184197	40.622111
ic295	3.183539	40.61525
ic296	3.184658	40.626861
ic297	3.221772	42.148778
ic298	3.188583	1.314722
ic298a	3.188472	1.315028
ic298b	3.188758	1.313389
ic299	3.184042	-13.109583
ic300	3.237783	42.415333
ic301	3.246586	42.222639
ic302	3.214242	4.707028
ic303	3.211353	-11.689944
ic304	3.250381	37.881833
ic305	3.251056	37.86
ic306	3.216725	-11.715694
ic307	3.229225	-0.241444
ic308	3.271064	41.18075
ic309	3.268414	40.804556
ic310	3.278606	41.324972
ic311	3.279647	40.003611
ic312	3.302392	41.754111
ic313	3.349417	41.893833
ic314,ngc1289	3.313836	-1.973333
ic315	3.319261	4.038556
ic316	3.355528	41.930556
ic317	3.315419	-12.740194
ic318	3.345508	-14.568222
ic319	3.391403	41.416361
ic320	3.433106	40.789028
ic321	3.408219	-14.985472
ic322	3.433464	3.680556
ic323	3.492653	41.855083
ic324,ngc1331	3.441192	-21.355306
ic325	3.513572	-7.046722
ic326	3.510169	-14.425556
ic327	3.519439	-14.692139
ic328	3.519708	-14.637861
ic329	3.533714	0.279444
ic330	3.535564	0.353389
ic331	3.538633	0.282556
ic332	3.543728	1.382556
ic333	3.567606	-4.584889
ic334	3.754744	76.638306
ic1963,ic335	3.591956	-34.447056
ic336	3.632511	23.363139
ic337	3.617861	-6.721194
ic338	3.62725	3.118778
ic339	3.633953	-18.397778
ic340	3.658086	-13.115111
ic341	3.682136	21.960194
ic342	3.780139	68.096361
ic343	3.66865	-18.443472
ic344	3.691536	-4.665861
ic345	3.685869	-18.314139
ic346	3.695739	-18.266972
ic347	3.709069	-4.298639
ic1985,ic348,lbn758,omipercloud	3.742831	32.162833
barnardsmeropenebula,ic349	3.772253	23.939806
ic350	3.743514	-11.80075
ic351	3.792503	35.046917
ic352	3.793731	-8.731833
ic353	3.883631	25.848
ic354	3.899419	23.147
ic355	3.896183	19.973917
ic356	4.129697	69.812444
ic357	4.062222	22.159111
ic358	4.061911	19.894944
ic359	4.207878	27.701972
ic359a,lbn782	4.311389	28.29
ic360,lbn786	4.150714	26.131194
ic361	4.314083	58.2495
ic362	4.278453	-12.200111
ic363	4.315394	3.033028
ic364	4.318528	3.188944
ic365	4.320594	3.348333
ic366	4.328206	2.359806
ic367	4.344719	-14.781056
ic368	4.378533	-12.615167
ic369	4.391172	-11.790083
ic370	4.400464	-9.394833
ic371	4.503497	-0.561
ic372	4.501178	-5.009972
ic373	4.511878	-4.87025
ic374	4.542431	16.634167
ic375	4.517539	-12.973972
ic376	4.520497	-12.433361
ic377	4.521261	-12.455083
ic378	4.524422	-12.29975
ic379	4.530814	-7.238361
ic380	4.528144	-12.927028
ic381,ngc1530a	4.74125	75.63975
ic382	4.632097	-9.519333
ic383	4.649453	9.892528
ic384	4.655078	-7.839111
ic385	4.658739	-7.097472
ic386,ngc1632	4.666272	-9.456222
ic387	4.695614	-7.086194
ic388	4.698147	-7.305528
ic389	4.699894	-7.311472
ic390	4.701075	-7.206444
ic391	4.955869	78.188833
ic392	4.773822	3.505556
ic393	4.797722	-15.525194
ic394	4.814086	-6.280194
ic395,ngc1671	4.826119	0.252861
ic396	4.966386	68.323389
ic397	5.018508	40.424889
ic398	4.970156	-7.78025
ic399	5.028892	-4.28875
ic400	5.062678	-15.819083
ic401	5.072122	-10.076528
ic402	5.104119	-9.107417
ic403	5.254358	39.972111
ic404	5.222111	9.754917
flamingstarnebula,ic405,lbn795	5.274856	34.356167
ic406	5.296944	39.886028
ic407	5.295169	-15.523444
ic2121,ic408	5.329128	-25.064333
ic409	5.325986	3.318389
ic410,lbn807	5.378333	33.366667
ic411	5.338503	-25.3245
ic2123,ic412	5.36575	3.486389
ic2124,ic413	5.366328	3.482167
ic414	5.365267	3.342028
ic415	5.356008	-15.542583
ic416	5.398994	-17.260417
ic417,lbn804	5.468333	34.423944
ic418	5.457831	-12.697278
ic419	5.51445	30.117917
ic420	5.535972	-4.50475
ic421	5.535717	-7.918333
ic2131,ic422	5.538486	-17.223861
ic423,lbn913	5.556114	-0.6145
ic424,lbn914	5.560344	-0.413139
ic425	5.619422	32.429667
ic426,lbn921	5.608717	-0.298306
ic427	5.605006	-6.616444
ic428	5.606725	-6.451556
ic429	5.638572	-7.0405
ic430	5.643325	-7.083111
ic431,lbn944	5.670564	-1.462806
ic432,lbn946	5.682217	-1.507
ic433	5.675375	-11.665583
flamenebula,ic434,lbn953,orionb	5.683578	-2.453778
ic435	5.716825	-2.312611
ic436	5.894467	38.624778
ic437	5.860389	-12.564972
ic438	5.883356	-17.876083
ic439	5.944308	32.022694
ic440	6.320364	80.068472
ic441	6.045175	-12.499139
ic442	6.603303	82.96825
gema,ic443,lbn844	6.277058	22.531667
ic444,lbn840	6.309444	23.313333
ic445	6.622569	67.859861
ic2167,ic446,lbn898	6.518383	10.459278
ic2169,ic447,lbn903	6.516756	9.897444
ic448,lbn931	6.545928	7.388639
ic449	6.761419	71.343833
ic450	6.870069	74.427083
ic451	6.881114	74.480722
ic452,ngc2296	6.810864	-16.901611
ic453	6.819847	-16.90675
ic454	6.85175	12.922028
ic455	7.582689	85.537194
ic456	7.004872	-30.163778
ic457,ngc2330	7.157889	50.152528
ic458	7.176153	50.118917
ic459	7.177414	50.177333
ic460	7.178964	50.202444
ic461	7.179178	50.081417
ic462	7.182169	50.180833
ic463	7.183581	50.117694
ic464	7.184653	50.136889
ic465,ngc2334	7.192681	50.24825
ic466	7.144111	-4.318
ic467	7.505108	79.872528
ic468	7.288611	-13.218694
ic469	7.933078	85.158917
ic470	7.392083	46.078667
ic471	7.726792	49.667556
ic472	7.73065	49.614194
ic473	7.706839	9.255278
ic474	7.768697	26.505111
ic475	7.785897	30.488806
ic476	7.787869	26.950972
ic477	7.868592	23.483028
ic478	7.894881	26.492694
ic479	7.906172	27.008833
ic480	7.923108	26.743333
ic481	7.984128	24.160639
ic482	7.996467	25.356972
ic483	7.997883	25.925333
ic484	8.000294	26.665861
ic485	8.005492	26.701444
ic486	8.005828	26.613528
ic487,ngc2494	7.985317	-0.637917
ic488	8.013753	25.901861
ic489	8.02715	25.996389
ic490	8.055589	25.811417
ic491	8.065278	26.520611
ic492	8.094072	26.168194
ic493	8.124331	25.134028
ic494	8.1067	1.036056
ic495	8.138728	9.013889
ic2229,ic496	8.162267	25.881611
ic497	8.168353	24.922083
ic498	8.158408	5.280694
ic499	8.754806	85.740028
ic500	8.211	-16.050806
ic501	8.313219	24.537417
ic502	8.367669	8.752611
ic503	8.369633	3.268056
ic504	8.378111	4.262417
ic505	8.389353	4.372472
ic506	8.391869	4.2995
ic507,ngc2590	8.417222	-0.591389
ic508	8.472864	25.124722
ic509	8.534306	24.010917
ic510	8.536278	-2.162222
ic511	8.680681	73.486667
ic512	9.063842	85.501694
ic513	8.551406	-12.355556
ic514	8.589522	-2.047056
ic515	8.592025	-1.901111
ic516	8.597436	-1.871222
ic517	8.606139	-2.055556
ic518	8.601931	0.692583
ic519	8.676225	2.611333
ic520	8.895072	73.490944
ic521	8.778878	2.537417
ic522	8.909697	57.166722
ic523	8.886478	9.148167
ic524	8.970231	-19.191917
ic525	9.022908	-1.853972
ic526	9.044661	10.841639
ic527	9.161606	37.601583
ic528	9.156264	15.796167
ic529	9.309111	73.759333
ic530	9.254714	11.885694
ic531	9.297447	-0.278472
ic532	9.317711	-16.754944
ic533	9.339833	-3.992028
ic534	9.354292	3.151139
ic535	9.371172	-1.040333
ic536	9.411139	25.110194
ic537	9.422947	-12.391778
ic538,ngc2885	9.455142	23.020111
ic539	9.485622	-2.549139
ic540	9.502869	7.90275
ic541	9.508553	-4.253667
ic542	9.518394	-13.181361
ic543	9.519194	-14.7725
ic544	9.598161	24.894861
ic545	9.601489	24.948944
ic546	9.580622	-16.384417
ic2494,ic547,ngc2947	9.601608	-12.436722
ic548	9.638694	9.445972
ic549	9.678675	3.95975
ic550	9.674606	-6.946056
ic551	9.683364	6.936083
ic552	9.687936	10.647
ic553	9.679203	-5.435361
ic554,ic555	9.699136	12.296278
ic556,ngc2984	9.727883	11.060861
ic557	9.734	10.988111
ic558	9.750097	29.452306
ic559	9.745525	9.615
ic560	9.764844	-0.268306
ic561	9.766336	3.145194
ic562	9.76775	-3.971167
ic563	9.772319	3.045583
ic564	9.772522	3.071361
ic565	9.797433	15.852556
ic566	9.832331	-0.231361
ic567	9.842717	12.784722
ic568	9.852314	15.730444
ic569	9.857819	10.920056
ic570	9.864161	15.75575
ic571	9.875436	15.775444
ic572	9.875781	15.826861
ic573	9.893381	-12.482111
ic574	9.907508	-6.953389
ic575	9.909147	-6.857556
ic576	9.918622	11.039556
ic577	9.934436	10.498861
ic578	9.937819	10.486083
ic579	9.944283	-13.774889
ic580,ngc3069	9.96575	10.432444
ic581	9.969883	15.946972
ic582	9.983397	17.817139
ic583	9.984744	17.821444
ic584	9.984758	10.361139
ic585	9.995589	12.988583
ic586	9.997306	-6.922833
ic587	10.051436	-2.400028
ic588	10.035289	3.057694
ic589	10.073306	-5.678917
ic590	10.097286	0.632944
ic591	10.124358	12.2745
ic592	10.132986	-2.49725
ic593	10.138336	-2.526806
ic594	10.142222	-0.666861
ic595	10.160589	11.00025
ic596	10.175375	10.042389
ic597	10.169989	-6.89925
ic598	10.213492	43.145528
ic599	10.220142	-5.629
ic600	10.286364	-3.497778
ic601	10.304247	7.038833
ic602	10.305481	7.049306
ic603	10.323625	-5.656167
ic604,ngc3220	10.395739	57.026861
ic605	10.373369	1.19825
ic606,ngc3217	10.392394	10.959722
ic607	10.402383	16.741889
ic608	10.405869	-6.039306
ic609	10.426508	-2.215222
ic610,ic611	10.441214	20.228194
ic612	10.451628	11.054889
ic613	10.452164	11.010722
ic614	10.447736	-3.46475
ic615	10.456106	11.079972
ic616	10.546544	15.860833
ic617,ngc3280b	10.545503	-12.637306
ic618,ngc3296	10.545944	-12.717417
ic619	10.563883	12.878361
ic620	10.559286	11.871389
ic621	10.555844	2.616139
ic622,ngc3279	10.578556	11.197333
ic623	10.589169	3.558389
ic624	10.604217	-8.333944
ic625	10.710569	-23.935611
ic626	10.615861	-7.023861
ic627	10.622192	-3.357806
ic628	10.626719	5.603694
ic629,ngc3312	10.617367	-27.565056
ic630	10.642669	-7.170528
ic631	10.649694	-7.052389
ic632	10.653275	-0.409472
ic633	10.656772	-0.389306
ic634	10.681914	5.991833
ic635	10.695917	15.643333
ic636	10.697386	4.330778
ic637	10.706089	15.359611
ic638	10.729994	15.895139
ic639	10.76445	16.930444
ic640	10.780681	34.767639
ic641	10.797058	34.672833
ic642	10.802258	18.188694
ic643	10.824217	12.201
ic644,ngc3398	10.858731	55.390972
ic645	10.835931	-6.042889
ic646	10.859772	55.465833
ic647	10.842914	-12.854806
ic648	10.850089	12.287389
ic649	10.847833	1.163889
ic650	10.844597	-13.442056
ic651	10.849558	-2.150361
ic652,ngc3421	10.849342	-12.448528
ic653	10.86855	-0.560778
ic654	10.897331	-11.725583
ic655	10.906178	-0.364972
ic656	10.918928	17.612889
ic657	10.964881	-4.904944
ic658	10.971183	8.241667
ic659	10.967739	-6.260528
ic660	10.974072	1.382917
ic661	10.980972	1.650639
ic662	10.989042	1.598833
ic663	11.010353	10.437194
ic664	11.012597	10.553056
ic665	11.008314	-13.866806
ic666	11.020781	10.481111
ic667	11.110153	15.088722
ic668	11.110989	15.040917
ic669	11.121269	6.302472
ic670	11.124669	6.71425
ic671	11.125444	0.783111
ic672	11.134231	-12.484167
ic673	11.157031	-0.097722
ic674	11.1851	43.633
ic675	11.1826	3.594222
ic676	11.211061	9.055833
ic677	11.232361	12.301083
ic678	11.235106	6.577194
ic679	11.276836	-13.972083
ic680	11.298528	-1.946444
ic681	11.308869	-12.140222
ic682,ngc3649	11.370761	20.208528
ic683	11.358828	2.751806
ic684,ngc3644	11.359131	2.810444
ic685	11.368478	17.753417
ic686	11.384797	5.644667
ic687	11.404814	47.847528
ic688	11.394511	-9.795556
ic689,ngc3661	11.394008	-13.831111
ic690	11.405725	-8.341972
ic691	11.445644	59.155417
ic692	11.431519	9.9875
ic693	11.446839	-5.004
ic694	11.47425	58.578472
ic695	11.466192	-11.715333
ic696	11.477756	9.098694
ic697	11.476236	-1.629583
ic698	11.4844	9.112056
ic699	11.485136	8.988583
ic700	11.487633	20.584917
ic701	11.516856	20.468944
ic702	11.515197	-4.922
ic703,ngc3704	11.501292	-11.546333
ic704,ngc3707	11.503211	-11.5435
ic705	11.548986	50.241861
ic706	11.553506	-13.338056
ic707	11.5624	21.380056
ic708	11.56645	49.062056
ic709	11.570706	49.043167
ic710	11.574281	25.876472
ic711	11.5796	48.956111
ic712	11.580364	49.077694
ic713	11.57895	16.846889
ic714,ngc3763	11.608386	-9.846694
ic715	11.615175	-8.377389
ic715nw	11.615058	-8.375806
ic715se	11.615261	-8.378722
ic716	11.650925	-0.206
ic717,ngc3779	11.647514	-10.58375
ic718	11.664658	8.874528
ic719	11.671808	9.009889
ic720	11.706194	8.767778
ic721	11.708022	-8.340333
ic722	11.712156	8.974222
ic723	11.716	-8.3325
ic724	11.726297	8.942472
ic725	11.724817	-1.667972
ic726	11.72925	33.391944
ic727	11.741278	10.783806
ic728	11.747353	-1.601333
ic729	11.755089	33.335806
ic730,ngc3849	11.759792	3.231833
ic731	11.755022	49.570417
ic732	11.766556	20.442778
ic732n	11.766508	20.447028
ic732s	11.766631	20.438917
ic733	11.766267	-8.155833
ic734	11.767722	-8.267778
ic735	11.803556	13.209389
ic736	11.805589	12.716583
ic737	11.807644	12.727389
ic738	11.815242	-4.681944
ic739	11.858692	23.862861
ic740,ngc3913	11.84415	55.353861
ic741	11.842158	-4.835889
ic742	11.850625	20.799722
ic743	11.889517	-13.264861
ic744	11.901319	23.192222
ic745	11.903408	0.136639
ic746	11.926425	25.889444
ic747	11.951361	-8.292333
ic748	11.957419	7.460944
ic749	11.976125	42.734028
ic750	11.981167	42.722472
ic751	11.981278	42.570333
ic752	11.9875	42.566833
ic753	11.986911	-0.523833
ic754	11.989875	-1.654528
ic755,ngc4019	12.019561	14.104306
ic756	12.049392	4.845861
ic757,ngc4068	12.066883	52.588278
ic758	12.069967	62.505361
ic759	12.085925	20.26
ic760	12.098197	-29.292083
ic761	12.09825	-12.673333
ic762	12.136656	25.757139
ic763	12.137586	25.8115
ic764	12.170608	-29.736806
ic765	12.175269	16.135194
ic766	12.181556	-12.65525
ic767	12.184092	12.104
ic768	12.196561	12.143722
ic769	12.208981	12.123806
ic770	12.217314	-4.553361
ic771	12.253678	13.184528
ic3067,ic772	12.254414	23.958167
ic773	12.302247	6.139556
ic774	12.314239	-6.766556
ic775	12.314908	12.912667
ic776	12.317472	8.856111
ic777	12.323267	28.309944
ic778,ngc4198	12.239458	56.011444
ic779	12.327425	29.883194
ic780	12.332883	25.771694
ic781	12.33425	14.961528
ic782	12.360269	5.76575
ic783	12.360775	15.745111
ic784	12.375014	-4.652694
ic785	12.383911	-13.223639
ic786	12.386375	-13.204667
ic787	12.423644	16.124194
ic788,ngc4405	12.435319	16.181
ic789	12.439033	7.460167
ic790,ngc4410c	12.443194	9.035472
ic791	12.449856	22.639583
ic792	12.452436	16.325389
ic793,ngc4445	12.471092	9.436194
ic794	12.469058	12.093306
ic795	12.475372	23.304944
ic796	12.490653	16.404778
ic797	12.531878	15.123944
ic798	12.542614	15.415389
ic799,ngc4520	12.563861	-7.375556
ic800	12.565739	15.354833
ic801	12.562486	52.254806
ic802	12.599342	74.301333
ic803	12.660281	16.588028
ic804	12.687769	-5.009111
ic805,ngc4611	12.690403	13.729528
ic806	12.702342	-17.349361
ic807	12.703469	-17.403556
ic808	12.698486	19.932111
ic3672,ic809	12.702406	11.754278
ic810	12.702522	12.596806
ic811,ngc4663	12.746403	-10.197833
ic812	12.747461	-4.434611
ic813	12.753289	23.036139
ic814	12.759483	-8.092194
ic815	12.772964	11.876611
ic816	12.779539	9.850556
ic3764,ic817	12.782444	9.857111
ic818	12.779042	29.735278
ic819,ngc4676a	12.769475	30.731917
ic820,ngc4676b	12.769789	30.72275
ic821	12.7906	29.787778
ic822	12.795992	30.077194
ic823	12.797461	27.209167
ic824,ngc4678	12.828292	-4.579722
ic825	12.838658	-5.363
ic826	12.855536	31.059639
ic827	12.865294	16.282861
ic828	12.871008	-8.132861
ic829	12.874286	-15.518528
ic830	12.854589	53.696306
ic831	12.878908	26.470417
ic832	12.899753	26.444056
ic833	12.943944	-6.733417
ic834	12.9385	26.358917
ic835	12.947856	26.487722
ic836	12.931672	63.612333
ic837	12.958669	26.512167
ic838	12.970436	26.426889
ic839	12.970847	28.125917
ic840	12.978342	10.6165
ic841	12.996483	21.813222
ic842	13.010986	29.019417
ic4088,ic843,ngc4913	13.028714	29.044667
ic844	13.055061	-30.521083
ic845	13.082617	12.079056
ic846	13.089197	23.095556
ic847,ngc4973	13.092264	53.685139
ic848	13.1171	16.007111
ic849	13.127414	-0.942472
ic850	13.130619	-0.868444
ic851	13.142872	21.049778
ic852	13.126878	60.157194
ic4205,ic853	13.144925	52.774278
ic854	13.163881	24.577556
ic855	13.176917	-4.484528
ic856	13.178225	20.536778
ic857	13.230603	17.07625
ic858	13.247761	17.226778
ic859	13.249244	17.225167
ic860	13.250981	24.618861
ic861	13.252061	34.328778
ic862	13.270939	20.047667
ic863	13.286778	-17.254472
ic864	13.285692	20.691722
ic865	13.293192	-5.833889
ic866	13.287986	20.691
ic867	13.288831	20.638083
ic868	13.291261	20.612333
ic869	13.291878	20.681083
ic870	13.291917	20.600111
ic871	13.299628	4.403417
ic872	13.283778	6.357083
ic873	13.304522	4.464306
ic874	13.316811	-27.628556
ic875	13.285436	57.539444
ic876	13.309606	4.486306
ic877	13.299269	6.082056
ic878	13.3001	6.120417
ic4222,ic879	13.327936	-27.428972
ic880	13.302044	6.112111
ic881	13.332319	15.850528
ic882	13.335261	15.898139
ic883	13.34315	34.1395
ic884	13.365253	-12.729722
ic885	13.375256	21.316417
ic886	13.399303	-4.395444
ic887	13.403317	-12.460417
ic888,ngc5136	13.414281	13.737861
ic889	13.443761	11.8695
ic890	13.473775	-16.092333
ic891	13.499978	0.305111
ic892	13.529411	-2.713056
ic893	13.529828	-2.611611
ic894	13.534672	17.048972
ic895,ngc5273	13.702317	35.654222
ic896	13.569506	4.868472
ic897	13.572069	17.848056
ic898	13.569281	13.280833
ic899	13.583183	-8.091639
ic900	13.578614	9.336861
ic901	13.595111	13.330917
ic902	13.600339	49.960833
ic903	13.640575	-0.227639
ic904	13.642281	0.540194
ic905	13.667481	23.142972
ic906	13.669442	23.341083
ic907	13.656392	51.051056
ic908	13.688594	-4.344194
ic909	13.680878	24.473278
ic910	13.685517	23.282056
ic911	13.690381	23.247472
ic912	13.69135	23.245444
ic913	13.691572	23.166944
ic914	13.694614	23.189028
ic915	13.724264	-17.332806
ic916	13.710597	24.465056
ic917	13.708681	55.636917
ic918	13.710503	55.529556
ic919	13.713194	55.521389
ic920	13.756853	-12.574167
ic921	13.718889	55.651222
ic922	13.715656	55.603889
ic923	13.720608	55.603139
ic924	13.760442	-12.455083
ic925	13.721139	55.615806
ic926	13.727575	55.631528
ic927	13.764553	-12.4645
ic928	13.73	55.567861
ic929	13.729172	55.633778
ic930	13.729319	55.646528
ic931	13.730331	55.623972
ic932	13.730889	55.64675
ic933	13.754489	23.218944
ic934,ic935	13.731219	55.656806
ic936	13.735708	55.706111
ic937	13.741369	55.630194
ic938	13.742014	55.627389
ic939	13.795314	3.411472
ic940	13.799364	3.449639
ic941	13.8099	24.015083
ic942	13.794761	56.621583
ic943	13.842258	3.194167
ic944	13.858575	14.092222
ic945	13.7855	72.070389
ic946	13.868989	14.116222
ic947	13.876639	0.818361
ic948	13.874086	14.091278
ic949	13.871322	22.521583
ic950	13.873944	14.489722
ic951	13.863114	50.978333
ic952	13.894978	3.377389
ic953	13.915894	-30.283306
ic954	13.832472	71.164556
ic955	13.9287	-30.261194
ic956	13.9113	20.721472
ic957	13.935656	-30.237639
ic958,ngc5360	13.927431	4.985056
ic959	13.934278	13.505833
ic960	13.933214	17.505833
ic960a	13.933081	17.499222
ic960b	13.933367	17.511556
ic961	13.929664	25.840361
ic962	13.953667	12.021333
ic963	13.95695	17.40775
ic964	13.961486	17.508722
ic965	13.963194	17.510528
ic966	13.970556	5.408278
ic967	13.973042	14.45725
ic968	14.010339	-2.907583
ic969	14.0295	-4.180389
ic970	14.042836	14.552556
ic971	14.064664	-10.140583
ic972	14.073864	-17.228194
ic973,ngc5467	14.108194	-5.481472
ic974	14.109544	-5.492417
ic975	14.119122	15.318083
ic976	14.145358	-1.161639
ic977	14.145014	-3.002444
ic978	14.149472	-2.973778
ic979	14.158992	14.831833
ic980	14.172892	-7.342583
ic981	14.174483	-4.171444
ic982	14.166414	17.696111
ic983	14.167881	17.733833
ic984	14.168822	18.364667
ic985	14.192464	-3.21975
ic986	14.190619	1.286528
ic987	14.192189	19.172278
ic988	14.242239	3.19025
ic989	14.247594	3.130889
ic990	14.263664	39.797917
ic991	14.296828	-13.872944
ic992	14.304142	0.891083
ic993	14.305172	11.216389
ic994	14.306286	11.195167
ic995	14.275308	57.810111
ic996	14.289464	57.629861
ic997	14.333125	-4.45125
ic998	14.338692	-4.416444
ic999	14.325742	17.875306
ic1000	14.327864	17.854694
ic1001	14.344353	5.427361
ic1002	14.345078	5.485778
ic1003	14.358267	5.073194
ic1004	14.350633	17.700583
ic1005,ngc5607,ngc5620	14.324083	71.588222
ic1006	14.383083	23.794333
ic1007	14.410164	4.559167
ic1008,ic4414	14.395164	28.347861
ic1009	14.438222	12.352917
ic1010	14.455656	1.025861
ic1011	14.467925	1.006306
ic1012,ic4431	14.452639	30.948222
ic1013	14.46635	25.866333
ic1014	14.471786	13.780222
ic1015	14.471986	15.420111
ic1016,ic4424,ngc5619b	14.458992	4.821611
ic1017	14.468675	25.868778
ic1018	14.470222	25.830528
ic1019	14.470411	25.947417
ic1020	14.480414	26.032278
ic1021	14.488092	20.654528
ic1022	14.500511	3.772861
ic1023	14.540317	-35.803583
ic1024	14.524222	3.009083
ic1025	14.524522	7.063917
ic1026,ngc5653	14.502894	31.2155
ic1027	14.496806	53.965028
ic1028	14.554564	41.650389
ic1029	14.540906	49.904611
ic1030,ngc5672	14.543983	31.670167
ic1031	14.573328	48.037444
ic1032	14.577633	47.967972
ic1033	14.578264	47.937806
ic1034	14.620481	14.665139
ic1035	14.636169	9.336028
ic1036	14.639664	18.111222
ic1037	14.640381	18.184028
ic1038	14.657619	11.928639
ic1039	14.674833	3.43275
ic1040	14.672981	9.476139
ic1041	14.677194	3.377028
ic1042	14.677506	3.469722
ic1043	14.678708	3.374028
ic1044	14.691394	9.430917
ic1045,ngc5731	14.669225	42.779556
ic1046	14.631506	69.014472
ic1047	14.705547	19.191833
ic1048	14.716111	4.889472
ic1049	14.6592	62.002944
ic1050	14.735311	18.012639
ic1051	14.736553	19.020222
ic1052	14.737253	20.614
ic1053	14.762008	16.946917
ic1054	14.775344	1.27475
ic1055,ic4491	14.790469	-13.716139
ic1056,ic1057	14.763625	50.394056
ic1058	14.820108	17.020944
ic1059	14.845156	-0.875806
ic1060	14.863153	-7.232639
ic1061	14.853956	18.757556
ic1062	14.854906	18.686972
ic1063	14.869728	4.682056
ic1065	14.822658	63.270556
ic1066	14.884128	3.296028
ic1067	14.884792	3.331778
ic1068	14.892478	3.077306
ic1069	14.846256	54.411167
ic1070	14.897578	3.484667
ic1071	14.903472	4.750028
ic1072	14.90365	4.841556
ic1073	14.903986	4.794389
ic1074	14.865922	51.264889
ic1075	14.913681	18.105972
ic1076	14.916561	18.037333
ic1077	14.956033	-19.213694
ic1078	14.941394	9.354528
ic1079	14.943378	9.36975
ic1080	14.966617	-6.723306
ic1081	14.981961	-19.239083
ic1082	14.981247	7.007306
ic1083	14.925947	68.408583
ic1084	15.0208	-7.474917
ic1085	15.045381	17.252528
ic1086	15.058103	17.114417
ic1087	15.112192	3.776833
ic1088	15.113172	3.791861
ic1089	15.123886	7.11675
ic1090	15.095319	42.682361
ic1091	15.137086	-11.140917
ic1092	15.1267	9.358222
ic1093	15.126567	14.548
ic1094	15.128389	14.625
ic1095	15.143069	13.670611
ic1096	15.139325	19.192111
ic1097	15.142028	19.184333
ic1098	15.107011	55.601667
ic1099	15.115181	56.509
ic1100,ngc5881	15.105783	62.980972
ic1101	15.18225	5.744778
ic1102	15.184708	4.293861
ic1103	15.193297	19.207778
ic1104	15.213856	-5.055611
ic1105	15.220531	4.287556
ic1106	15.2323	4.710972
ic1107	15.235822	4.714417
ic1108,ngc5882	15.280556	-45.649306
ic1109	15.284439	5.256111
ic1110	15.201408	67.362583
ic1111,ngc5876	15.158767	54.5065
ic1112	15.296486	7.218278
ic1113	15.304197	12.488667
ic1114	15.190469	75.426694
ic1115	15.37195	-4.473861
ic1116	15.365353	8.423778
ic1117	15.406361	15.488583
ic1118,ic4543	15.416536	13.445083
ic1119	15.428967	-3.656306
ic1120	15.4364	18.872333
ic1121	15.462239	6.803889
ic1122	15.489742	7.617417
ic1123	15.481697	42.898528
ic1124	15.500242	23.638417
ic1125,ic1128	15.551558	-1.62825
ic1126	15.583561	4.990417
ic1127,ic4553	15.582569	23.503139
ic1129	15.533561	68.246333
ic1130	15.628897	17.244417
ic1131	15.647694	12.080639
ic1132	15.668544	20.680611
ic1133	15.686664	15.573417
ic1134	15.749583	16.962111
ic1135	15.759642	17.700083
ic1136	15.792886	-1.545278
ic1137	15.809056	8.587917
ic1138	15.804381	26.206222
ic1139	15.490583	82.583861
ic1140	15.823683	19.113444
ic1141	15.829706	12.399333
ic1142	15.840533	18.139583
ic1143	15.515544	82.455778
ic1144	15.856025	43.417667
ic1145	15.735708	72.431167
ic1146	15.806133	69.385583
ic1147	15.836558	69.560056
ic1148,ngc6020	15.952261	22.404583
ic1149	15.968883	12.070278
ic1150	15.971822	15.874528
ic1151	15.97565	17.441472
ic1152	15.945367	48.095
ic1153	15.950836	48.168389
ic1154	15.874614	70.375083
ic1155	16.009933	15.685639
ic1156	16.010378	19.723222
ic1157	16.015628	15.526444
ic1158	16.026133	1.707833
ic1159	16.017072	15.419972
ic1160	16.017364	15.494694
ic1161	16.021339	15.645417
ic1162	16.021203	17.677833
ic1163	16.025153	15.503917
ic1164	15.917419	70.586972
ic1165	16.035611	15.693889
ic1166	16.035806	26.327222
ic1167	16.064683	14.946444
ic1168	16.065469	14.902417
ic1169	16.070397	13.744028
ic1170	16.075469	17.721472
ic1171	16.081067	17.978222
ic1172,ngc6044	16.083244	17.870361
ic1173	16.086822	17.422861
ic1174	16.090783	15.025333
ic1175	16.089617	18.163111
ic1176,ngc6056	16.092022	17.963639
ic1177	16.088831	18.315361
ic1178	16.092533	17.601444
ic1179,ngc6050b	16.089506	17.754194
ic1180	16.091697	18.149667
ic1181	16.092736	17.593694
ic1182	16.093556	17.802139
ic1183,ngc6054	16.093931	17.767889
ic1184	16.095222	17.79
ic1185	16.095747	17.717028
ic1186	16.095617	17.362167
ic1187	15.986161	70.556972
ic1188	16.102133	17.46
ic1188a	16.102028	17.460806
ic1188b	16.1023	17.461639
ic1189	16.104119	18.182889
ic1190	16.097892	18.220528
ic1191	16.107986	18.267889
ic1192	16.109203	17.775639
ic1193	16.108944	17.713861
ic1194	16.110931	17.761194
ic1195	16.111356	17.191806
ic1196	16.132881	10.779639
ic1197	16.138131	7.5385
ic1198	16.143436	12.330944
ic1199	16.176208	10.040361
ic1200,ngc6079	16.074781	69.665778
ic1201	16.094903	69.593806
ic1202,ngc6081	16.215794	9.867111
ic1203	16.254444	-22.370583
ic1204	16.120967	69.931472
ic1205	16.237756	9.537194
ic1206	16.253631	11.297389
ic1207	16.324089	-29.651111
ic1208	16.263303	36.527333
ic1209	16.311006	15.558361
ic1210	16.241708	62.536694
ic1211	16.281106	53.006028
ic1212	16.258542	64.224806
ic1213,ngc6172	16.369528	-1.514861
ic1214	16.269917	65.968778
ic1215	16.259758	68.397667
ic1216	16.265383	68.349889
ic1217	16.267806	69.6765
ic1218	16.276972	68.202639
ic1219	16.407625	19.482583
ic1220	16.493972	8.450722
ic1221	16.578231	46.392056
ic1222	16.585889	46.213917
ic1223	16.595128	49.220528
ic1224	16.715636	19.254361
ic1225	16.614589	67.629417
ic1226,ic1232	16.685158	46.004056
ic1227,ngc6206	16.668861	58.617361
ic1228	16.7018	65.5855
ic1229	16.749672	51.308083
ic1230	16.750411	51.259583
ic1231	16.783061	58.423167
ic1233,ngc6247	16.805622	62.976417
ic1234	16.880808	56.877778
ic1235	16.867675	63.115806
ic1236	16.974889	20.041472
ic1237	16.937792	55.026472
ic1238	17.008375	23.07675
ic1239,ngc6276	17.012525	23.044
ic1240	17.016353	61.050444
ic1241	17.024506	63.691111
ic1242	17.145244	4.049889
ic1243	17.173486	10.766611
ic1244	17.176031	36.303306
ic1245	17.210167	38.020444
ic1246	17.236744	20.237306
ic1247	17.272817	-12.780889
ic1248	17.194494	59.995611
ic1249	17.248644	35.520111
ic1250	17.241436	57.416778
ic1251	17.17025	72.4105
ic1252,ic4649	17.263994	57.366806
ic1253,ngc6347	17.331853	16.660694
ic1254	17.192614	72.402
ic1255	17.384831	12.695444
ic1256	17.396475	26.486528
ic1257	17.452328	-7.093083
ic1258	17.454828	58.485472
ic1259	17.457167	58.516667
ic1260	17.458811	58.475861
ic1261	17.389822	71.263639
ic1262	17.550561	43.759611
ic1263	17.552	43.822083
ic1264	17.554678	43.629222
ic1265	17.610953	42.088417
ic1266	17.759806	-46.089861
ic1267	17.646081	59.373139
ic1268	17.844247	17.209444
ic1269	17.868333	21.569639
ic1270	17.799167	62.223444
ic1271	18.086975	-24.410528
ic1272	18.082153	25.129194
ic1273	18.084097	25.132111
ic1274,lbn33	18.164175	-23.648222
ic1275	18.168664	-23.761222
ic1276	18.178964	-7.207583
ic1277	18.174247	31.003167
ic1278	18.178236	31.149917
ic1279	18.187606	36.007778
ic1280,ngc6581	18.205117	25.662361
ic1281	18.193917	35.992222
ic1282	18.234792	21.102194
ic1283,lbn47	18.288014	-19.762222
ic1284	18.294342	-19.672028
ic1285	18.269492	25.100333
ic1286	18.270631	55.591
ic1287,lbn75	18.523803	-10.795806
ic1288	18.489572	39.713361
ic1289	18.500636	39.964028
ic1290	18.643142	-24.096833
ic1291	18.564603	49.278611
ic1292	18.744569	-27.816278
ic1293	18.693514	56.317778
ic1294	18.830681	40.209389
ic1295	18.910314	-8.827028
ic1296	18.888564	33.066583
ic1297	19.289833	-39.613056
ic1298	19.309914	-1.596194
ic1299	19.378342	20.739556
ic1300,ngc6798	19.400881	53.624778
ic1301,ic4867	19.442217	50.125278
ic1302	19.514692	35.78525
ic1303	19.525017	35.876611
ic1304	19.592914	41.111833
ic1305	19.65475	20.194278
ic1306	19.694775	37.685194
ic1307	19.708917	27.752639
ic1308	19.751456	-14.72025
ic1309	20.050422	-17.232083
ic1310,lbn181	20.166939	34.968889
ic1311	20.17995	41.173944
ic1312	20.280972	18.045972
ic1313	20.312128	-16.945972
ic1314	20.297222	25.089778
ic1315	20.289431	30.689083
ic1316	20.373844	6.501694
ic1317	20.387664	0.664722
gamcyg,ic1318	20.370469	40.256694
ic1319	20.433869	-18.504083
ic1320	20.440461	2.909722
ic1321	20.469736	-18.2915
ic1322	20.502356	-15.227833
ic1323	20.508056	-15.181944
ic1324	20.536753	-9.056111
ic1325,ngc6928	20.547283	9.926417
ic1327	20.594797	-0.005778
ic1328	20.699178	-19.633056
ic1329	20.728364	15.597417
ic1330	20.770817	-14.023222
ic1331	20.796881	-9.995944
ic1332	20.864275	-13.711528
ic1333,ic1334	20.871444	-16.28575
ic1335	20.885033	-16.335444
ic1336	20.918033	-18.038722
ic1337	20.947972	-16.585833
ic1338	20.9494	-16.492611
ic1339	20.965422	-17.942833
ic1340	20.935625	31.047861
ic1341	21.004633	-13.976333
ic1342	21.007067	-14.495861
ic1343	21.01685	-15.403694
ic1344	21.021236	-13.380278
ic1345	21.022833	-13.397611
ic1346	21.02695	-13.960694
ic1347	21.028997	-13.313306
ic1348	21.028919	-13.358
ic1349	21.030681	-13.2655
ic1350,ic1354	21.031192	-13.852667
ic1351	21.031233	-13.201861
ic1352	21.031917	-13.384083
ic1353	21.032311	-13.272833
ic1355	21.032886	-13.173
ic1356	21.048056	-15.811583
ic1357	21.099253	-10.71625
ic1358	21.108169	-16.204444
ic1359	21.145283	12.484278
ic1360	21.180644	5.071361
ic1361	21.191428	5.054333
ic1362	21.197958	2.328972
ic1363	21.177894	46.870056
ic1364	21.223522	2.769722
ic1365	21.232197	2.565389
ic1366	21.235561	1.776111
ic1367	21.236028	2.993806
ic1368	21.236831	2.178
ic1369	21.202511	47.7685
ic1370	21.253964	2.192028
ic1371	21.337681	-4.876528
ic1372	21.338081	-5.604583
ic1373	21.343681	1.092417
ic1374	21.350736	1.712972
ic1375	21.349942	3.985417
ic1376	21.411417	-5.742444
ic1377	21.424064	4.314222
ic1378	21.381031	55.464306
ic1379	21.433683	3.097389
ic1380	21.453058	2.717667
ic1381	21.459361	-1.188611
ic1382,ngc7056	21.368767	18.665667
ic1383	21.461011	-1.102167
ic1384	21.464742	-1.368556
ic1385	21.480886	-1.070111
ic1386	21.493731	-21.195694
ic1387	21.492908	-1.350917
ic1388	21.497828	-0.631278
ic1389	21.535511	-18.018361
ic1390	21.540217	-1.862528
ic1391	21.583444	-0.511444
ic1392	21.592414	35.398333
ic1393	21.670625	-22.411389
ic1394	21.670286	14.633028
ic1395	21.694836	4.104528
ic1396,lbn451,lbn452	21.649339	57.489056
ic1397	21.733975	-4.884806
ic1398	21.764286	9.475333
ic1399	21.769142	4.402222
ic1400	21.737856	52.967028
ic1401	21.783192	1.71275
ic1402	21.749714	53.2625
ic1403	21.841411	-2.716167
ic1404	21.848994	-9.266583
ic1405	21.847178	2.020806
ic1406	21.851353	1.987056
ic1407	21.873178	3.427167
ic1408	21.885839	-13.346778
ic1409	21.888778	-7.499861
ic1410	21.933928	-2.900278
ic1411	21.933497	-1.517056
ic1412	21.971794	-17.176167
ic1413	21.974058	-3.102417
ic1414	21.971681	8.423806
ic1415	21.978511	1.350361
ic1416	21.980411	1.451556
ic1417	22.006003	-13.147361
ic1418	22.033311	4.384333
ic1419	22.049678	-9.920972
ic1420	22.042214	19.750111
ic1421	22.051119	-9.978167
ic1422	22.050017	2.598889
ic1423	22.053525	4.297583
ic1424	22.052608	11.197139
ic1425	22.056808	2.594917
ic1426	22.064244	-9.919306
ic1427	22.059767	15.106778
ic1428	22.074353	2.630861
ic1429	22.117347	10.109222
ic1430	22.12495	-13.581194
ic1431	22.127667	-13.513389
ic1432	22.167769	3.689583
ic1433	22.202833	-12.765278
ic1434	22.178378	52.850083
ic1435	22.223969	-22.096694
ic1436	22.230956	-10.191778
ic1437	22.262497	2.065944
ic1438	22.274747	-21.430694
ic1439	22.277817	-21.485944
ic1440	22.275894	-16.016444
ic1441	22.255317	37.3015
ic1442	22.267036	53.991333
ic1443	22.317683	-20.939917
ic1444	22.373311	5.139167
ic1445	22.425092	-17.243306
ic1446	22.484639	-1.184917
ic1447	22.499944	-5.119889
ic1448,ngc7308	22.575594	-12.933861
ic1449	22.585278	-8.765333
ic1450	22.632758	34.5355
ic1451	22.768739	-10.369417
ic1452,ngc7374b	22.766442	10.8675
ic1453	22.781731	-13.449611
ic1454	22.706947	80.442222
ic1455	22.896128	1.371972
ic1456	22.921719	-12.732
ic1457	22.923267	-5.56275
ic1458,ngc7441	22.944828	-7.379056
ic1459,ic5265	22.952947	-36.462222
ic1460	22.951133	4.677028
ic1461	22.976194	15.172778
ic1462	22.976986	8.441306
ic1463	22.989147	-10.530861
ic1464	23.053222	-8.990833
ic1464a	23.053356	-8.992972
ic1464b	23.053067	-8.989167
ic1465	23.048111	16.582472
ic1466	23.060847	-2.775444
ic1467	23.080475	-3.229944
ic1468	23.085436	-3.2045
ic1469	23.107964	-13.536583
ic1470	23.086169	60.244083
ic1471	23.145792	-12.639444
ic1472	23.151856	17.259139
ic1473	23.184836	29.643444
ic1474	23.214242	5.806361
ic1475	23.23395	-28.422444
ic1476	23.237875	30.551472
ic1477,ngc7596	23.286667	-6.912
ic1478,ngc7594	23.303867	10.298306
ic1479	23.312892	-10.39925
ic1480,ngc7607	23.316456	11.341722
ic1481	23.323644	5.906167
ic1482	23.347089	1.739028
ic1483,ngc7638	23.375867	11.328806
ic1484	23.377761	11.384472
ic1485,ngc7639	23.380064	11.372861
ic1486,ngc7648	23.398339	9.667472
ic1487,ngc7649	23.405581	14.647139
ic1488	23.427375	15.354417
ic1489	23.442258	-12.5165
ic1490,ic1524	23.986311	-4.127
ic1491	23.490192	-16.316611
ic1492	23.510028	-3.039917
ic1493	23.507642	14.458861
ic1494	23.512817	-12.724528
ic1495,ic5327	23.513261	-13.485444
ic1496	23.514864	-2.934306
ic1497	23.480581	11.987
ic1498	23.531569	-5.006972
ic1499	23.532508	-13.439694
ic1500	23.5526	4.552528
ic1501	23.577794	-3.152833
ic1502	23.6057	75.648139
ic1503	23.640864	4.801417
ic1504	23.688747	4.017472
ic1505	23.693642	-3.565083
ic1506	23.746781	4.735667
ic1507	23.759214	1.68875
ic1508	23.765297	12.06175
ic1509	23.787967	-15.306417
ic1510	23.842444	2.073333
ic1511	23.850125	27.060861
ic1512	23.850397	27.027139
ic1513	23.891494	11.317611
ic1514,ngc7776	23.9046	-13.586444
ic1515	23.934419	-0.988528
ic1516	23.935303	-0.916528
ic1517	23.938558	-0.305611
ic1518	23.9517	12.464972
ic1519	23.952325	12.457556
ic1520	23.965128	-14.039333
ic1521	23.983239	-7.146778
ic1522	23.984292	1.719889
ic1523,ic5368	23.985167	6.873056
ic1525	23.987708	46.889667
ic1526	0.025422	11.345889
ic1527	0.039333	4.08975
ic1528	0.084825	-7.093417
ic1529	0.086992	-11.502806
ic1530,ngc7831	0.122092	32.60925
ic1531	0.159883	-32.277
ic1532	0.164667	-64.372083
ic1533	0.176781	-7.415139
ic1534	0.229289	48.151361
ic1535	0.232594	48.157972
ic1536	0.238614	48.143278
ic1537	0.264242	-39.262083
ic1538	0.300433	30.029278
ic1539,ngc70	0.306261	30.079583
ic1540	0.330208	23.772611
ic1541	0.333878	21.99975
ic1542	0.344775	22.592444
ic1543	0.348736	21.866028
ic1544	0.354861	23.090861
ic1545	0.355808	21.983444
ic1546	0.358064	22.505861
ic1547	0.359914	22.506444
ic1548	0.365322	22.006306
ic1549	0.380508	6.964278
ic1550	0.407681	38.185639
ic1551	0.459858	8.8775
ic1552	0.495475	21.476833
ic1553	0.544478	-25.607528
ic1554	0.552042	-32.258361
ic1555	0.575733	-30.017861
ic1556	0.584142	-9.368417
ic1557	0.592922	-2.876417
ic1558	0.596408	-25.374417
ic1559,ngc169a	0.614536	23.984972
ic1560	0.627564	2.671556
ic1561	0.642358	-24.339944
ic1562	0.642767	-24.274056
ic1563,ngc191a	0.650067	-9.014583
ic1564	0.651425	6.021056
ic1565,ic1567	0.657297	6.73425
ic1566	0.659267	6.815139
ic1568	0.665544	6.848583
ic1569	0.67445	6.719694
ic1570	0.676139	6.752667
ic1571	0.677181	-0.330667
ic1572	0.686694	16.2375
ic1573	0.702906	-23.591583
ic1574	0.717728	-22.246889
ic1575	0.725933	-4.117833
ic1576	0.737264	-25.109278
ic1578	0.740536	-25.076833
ic1579	0.759014	-26.565444
ic1580	0.772592	29.936611
ic1581	0.762867	-25.920167
ic1582	0.771339	-24.279333
ic1583	0.786194	23.073833
ic1584	0.788494	27.827667
ic1585	0.787306	23.053556
ic1586	0.798978	22.372889
ic1587	0.812028	-23.561667
ic1588	0.849364	-23.557944
ic1589	0.866489	-34.422056
ic1590	0.880611	56.643028
ic1591,ngc276	0.868492	-22.680139
ic1592	0.890844	5.770389
ic1593	0.911008	32.519472
ic1594	0.895925	-47.647472
ic1595	0.896403	-45.186639
ic1596	0.911897	21.522639
ic1597	0.892247	-58.107139
ic1598	0.911603	5.773806
ic1599	0.909114	-23.494917
ic1600	0.917844	-23.524889
ic1601	0.926344	-24.153389
ic1602	0.931081	-9.985667
ic1603	0.949911	-45.412944
ic1604	0.966375	-16.230056
ic1605	0.960456	-48.902667
ic1606	0.972825	-12.1785
ic1607	0.980239	0.58725
ic1608	0.990103	-34.328944
ic1609	0.996283	-40.333556
ic1610	1.028494	-15.567778
ic1611	0.996639	-72.332333
ic1612	0.999614	-72.370722
ic1613	1.079942	2.117778
ic1614	1.085267	33.189806
ic1615	1.068622	-51.133056
ic1616	1.082272	-27.429361
ic1617	1.071333	-51.032806
ic1618	1.098883	32.412167
ic1619	1.1229	33.067278
ic1620	1.120625	13.955111
ic1621	1.106286	-46.7255
ic1622	1.126853	-17.538639
ic1623	1.129772	-17.507028
ic1623a	1.129639	-17.507222
ic1623b	1.129878	-17.506972
ic1624	1.0894	-72.042528
ic1625	1.128503	-46.907583
ic1626	1.103731	-73.296111
ic1627	1.136344	-46.094056
ic1628	1.146536	-28.582333
ic1629	1.155056	2.567472
ic1630	1.137992	-46.754028
ic1631	1.145797	-46.475806
ic1632	1.178717	17.68325
ic1633	1.165439	-45.931194
ic1634	1.184386	17.663056
ic1635	1.184314	17.652028
ic1636	1.193044	33.365389
ic1637	1.18365	-30.438528
ic1638	1.206058	33.364528
ic1639	1.196264	-0.664361
ic1640	1.197583	-0.630361
ic1641	1.160886	-71.768972
ic1643	1.202397	-0.410194
ic1644	1.153614	-73.194111
ic1645	1.207594	15.750083
ic1646	1.212175	15.707806
ic1647	1.220725	38.885278
ic1648	1.228367	33.218222
ic1649	1.197483	-55.857333
ic1650	1.205303	-50.401722
ic1651	1.224322	2.069167
ic1652	1.248961	31.9485
ic1653,ngc443	1.252108	33.377333
ic1654	1.2533	30.194833
ic1655	1.198361	-71.330611
ic1656,ngc447	1.260453	33.067722
ic1657,ic1663	1.235283	-32.650889
ic1658,ngc444	1.263778	31.08025
ic1659	1.268339	30.349083
ic1660	1.210464	-71.76175
ic1661,ngc451	1.270111	33.064111
ic1662	1.209097	-73.45675
ic1664	1.238475	-69.811528
ic1665	1.295808	34.701667
ic1666	1.331497	32.467333
ic1667	1.311764	-17.050222
ic1668	1.31475	33.173056
ic1669	1.335233	33.18475
ic1670	1.314111	-16.802778
ic1670a	1.313567	-16.803444
ic1670b	1.314681	-16.803444
ic1672	1.343944	29.698833
ic1673	1.346208	33.044944
ic1674	1.321789	-50.963583
ic1675	1.349972	34.248611
ic1676	1.349608	30.259472
ic1677	1.351969	33.216139
ic1678	1.350703	5.560528
ic1679	1.362389	33.493611
ic1680	1.364222	33.2825
ic1681	1.355922	0.090389
ic1682	1.370361	33.260278
ic1683	1.3775	34.436944
ic1684	1.381444	33.413611
ic1685	1.385167	33.189444
ic1686,ngc499	1.386528	33.460556
ic1687	1.388639	33.275278
ic1688	1.391139	33.083056
ic1689	1.396628	33.055333
ic1690	1.397094	33.156278
ic1691	1.407167	33.406944
ic1692	1.410989	33.235806
ic1693	1.400667	-1.657028
ic1694	1.413278	1.607167
ic1695	1.418786	8.6995
ic1696	1.414544	-1.617056
ic1697	1.417483	0.444361
ic1698,ic1699	1.422817	14.838722
ic1701	1.430667	18.184472
ic1702	1.432303	16.601806
ic1703,ngc557	1.440319	-1.638722
ic1704	1.452647	14.776278
ic1705	1.445789	-3.501472
ic1706	1.458617	14.819556
ic1707	1.466756	37.117056
ic1708	1.415578	-71.184444
ic1709,ngc568	1.465836	-35.717694
ic1710,ngc575	1.512956	21.440417
ic1711	1.51535	17.188556
ic1712,ngc584	1.522431	-6.868056
ic1713	1.5455	35.324472
ic1714	1.548103	-13.024972
ic1715	1.559483	12.585444
ic1716	1.557458	-12.307944
ic1717	1.541758	-67.536833
ic1718	1.640764	33.366528
ic1719	1.626644	-33.924083
ic1720	1.672664	-28.91275
ic1721	1.690122	8.525528
ic1722	1.717419	-34.187722
ic1723	1.720606	8.889361
ic1724	1.719356	-34.241889
ic1725	1.753286	21.776556
ic1726	1.755464	4.618528
ic1727	1.791636	27.333361
ic1728	1.795692	-33.6015
ic1729	1.798683	-26.892139
ic1730	1.832761	22.012111
ic1731	1.836761	27.196167
ic1732	1.846639	35.93275
ic1733	1.845247	33.082028
ic1734	1.821403	-32.742611
ic1735	1.847706	33.092333
ic1736	1.848111	18.302778
ic1737	1.861867	36.251194
ic1738	1.852194	-9.792028
ic1739	1.841556	-34.055583
ic1740	1.814322	-30.085972
ic1741	1.865758	-16.788028
ic1742	1.887286	22.721389
ic1743,ngc716	1.883244	12.708472
ic1744,ngc719	1.894122	19.840417
ic1745	1.883081	-16.669
ic1746	1.906753	4.803889
ic1747	1.959925	63.321778
ic1748	1.935794	17.641278
ic1749	1.936417	6.744944
ic1750	1.938489	4.076278
ic1751,ngc741	1.939175	5.628944
ic1752	1.954283	28.6135
ic1753	1.955364	28.58925
ic1754	1.947189	4.025611
ic1755	1.952719	14.549889
ic1756	1.951483	-0.46825
ic1757	1.953156	-0.473972
ic1758	1.947914	-16.542056
ic1759	1.965378	-32.987056
ic1760	1.956856	-31.988333
ic1761	1.981192	0.568306
ic1762	1.963511	-33.239806
ic1763	1.986597	-27.810694
ic1764	2.006492	24.580556
ic1765,ngc783	2.018503	31.882472
ic1766,ngc785	2.027778	31.8265
ic1767	1.999828	-11.078972
ic1768	2.013853	-25.026694
ic1769	2.015256	-31.919778
ic1770	2.037331	9.980944
ic1771	2.037739	9.968583
ic1772	2.045258	7.745528
ic1773,ngc804	2.067253	30.832861
ic1774	2.066389	15.318056
ic1775	2.088206	13.505722
ic1776	2.087561	6.106833
ic1777	2.102417	15.209472
ic1779	2.107203	3.705972
ic1780	2.114211	14.721917
ic1781	2.114664	-0.518083
ic1782,ngc823	2.122236	-25.441889
ic1783	2.168369	-32.939861
ic1784	2.270219	32.6495
ic1785	2.272511	32.666528
ic1786	2.268231	5.145472
ic1788	2.263878	-31.201
ic1789	2.29755	32.396028
ic1790	2.293831	12.508972
ic1791	2.294817	12.470611
ic1792	2.316969	34.462389
ic1793	2.359	32.5445
ic1794	2.358381	15.761639
ic1795,lbn645	2.442211	62.041639
ic1796	2.379811	-41.371083
ic1797	2.424414	20.395333
ic1798	2.437642	13.430778
ic1799	2.479419	45.970639
ic1800	2.475322	31.409667
ic1801	2.470208	19.583333
ic1802	2.487217	23.082694
ic1803	2.497206	23.108583
ic1804	2.49845	23.097083
ic1805,lbn654	2.544864	61.456889
ic1806	2.493042	22.943222
ic1807	2.508611	22.949722
ic1808,ngc963	2.508689	-4.215417
ic1809	2.527875	22.917194
ic1810	2.490786	-43.076333
ic1811	2.510608	-34.264167
ic1812	2.492161	-42.811361
ic1813	2.513747	-34.220889
ic1814,ngc964	2.518275	-36.034667
ic1815	2.572222	32.429472
ic1816	2.530833	-36.672056
ic1817	2.563944	11.203333
ic1818	2.56865	-11.04075
ic1819	2.594953	4.051806
ic1820	2.597964	6.040611
ic1821	2.607258	13.779556
ic1822	2.595097	-8.562806
ic1823	2.643606	32.069694
ic1824,ngc1027	2.709739	61.594361
ic1825	2.648786	9.097361
ic1826,ic1830	2.650986	-27.443139
ic1827	2.662906	1.558278
ic1828,ngc1036	2.674719	19.297111
ic1829	2.675775	14.297944
ic1831	2.732333	62.411639
ic1832	2.69935	19.030083
ic1833	2.694083	-28.171278
ic1834	2.713358	3.084167
ic1835	2.730319	14.889583
ic1836	2.723183	3.105389
ic1837,ngc1072	2.725364	0.306806
ic1838	2.745275	19.455111
ic1839	2.745253	15.240083
ic1840,ngc1105	2.728328	-15.705583
ic1841	2.760064	18.928917
ic1842	2.756506	11.458111
ic1843	2.756839	2.880528
ic1844	2.763722	3.230306
ic1845	2.732472	-27.968917
ic1846,ngc1109	2.795439	13.255333
ic1847	2.798242	14.505111
ic1848,lbn667	2.852942	60.402472
ic1849	2.795731	9.356806
ic1850,ngc1111	2.810931	13.259528
ic1851	2.862756	58.314306
ic1852,ngc1112	2.816769	13.22375
ic1853	2.801186	-13.993111
ic1854	2.822422	19.303917
ic1855	2.817864	13.442889
ic1856	2.814111	-0.767389
ic1857	2.827478	14.619806
ic1858	2.819003	-31.289583
ic1859	2.817756	-31.1725
ic1860	2.826031	-31.189111
ic1861	2.885272	25.490389
ic1862	2.866333	-33.340167
ic1863	2.914094	8.784389
ic1864	2.894253	-34.197639
ic1865	2.922272	8.828167
ic1866	2.914719	-15.652556
ic1867	2.931175	9.311833
ic1868	2.934958	9.378833
ic1869	2.969914	5.836583
ic1870	2.964869	-2.347083
ic1871,lbn675	2.956053	60.672361
ic1872	3.076281	42.810667
ic1873	3.064689	9.61325
ic1874	3.106106	36.014528
ic1875	3.065733	-39.440417
ic1876	3.075636	-27.4605
ic1877	3.052661	-50.511917
ic1878	3.061167	-52.108028
ic1879	3.064569	-52.11775
ic1880	3.10795	-9.731472
ic1881,ngc1213	3.154808	38.649444
ic1882	3.130361	3.147889
ic1883,ngc1212	3.161731	40.893083
ic1885	3.111231	-32.863639
ic1886	3.134233	-4.399833
ic1890	3.166231	19.208056
ic1891	3.170006	19.606556
ic1892	3.140897	-23.055778
ic1893	3.171269	19.616861
ic1894	3.173742	19.606611
ic1895	3.160061	-25.253583
ic1896	3.131256	-54.214472
ic1897	3.179425	-10.796056
ic1898	3.172164	-22.404861
ic1899	3.203642	-25.304917
ic1900	3.265342	37.154111
ic1901	3.267392	37.112444
ic1902	3.270117	37.177444
ic1903	3.219542	-50.569833
ic1904	3.250214	-30.708028
ic1905	3.313333	41.365444
ic1906	3.268236	-34.360639
ic1907,ngc1278	3.331708	41.563389
ic1908	3.251472	-54.819972
ic1909	3.288894	-33.690056
ic1910	3.299386	-21.43475
ic1911	3.346994	35.321806
ic1912	3.278731	-50.654889
ic1913	3.326261	-32.465028
ic1914	3.323678	-49.599722
ic1915	3.331097	-50.691194
ic1916	3.337922	-49.041917
ic1917	3.3701	-53.185194
ic1918	3.438303	4.541028
ic1919	3.433956	-32.894556
ic1920	3.406778	-52.713583
ic1921	3.411697	-50.698
ic1922	3.411953	-50.740528
ic1923	3.414622	-50.555833
ic1924	3.418797	-51.703444
ic1925	3.421025	-51.256889
ic1926	3.421953	-51.701056
ic1927	3.422136	-51.719444
ic1928	3.458106	-21.560167
ic1929	3.423847	-51.267194
ic1930	3.479517	4.383556
ic1931	3.4827	1.750722
ic1932	3.431675	-51.343167
ic1933	3.427747	-52.7855
ic1934	3.520561	42.792278
ic1935	3.437028	-50.010444
ic1936	3.441122	-51.323194
ic1937	3.446567	-48.702556
ic1938	3.4529	-53.009889
ic1939	3.462381	-51.070917
ic1940	3.461761	-52.139444
ic1941	3.537483	24.383722
ic1942	3.464806	-52.676944
ic1943,ngc1411	3.645797	-44.100611
ic1944	3.494444	-47.996167
ic1945	3.487933	-52.627167
ic1946	3.489497	-52.619333
ic1947	3.509117	-50.338528
ic1948	3.513903	-47.964861
ic1949	3.514672	-47.97925
ic1950	3.517922	-50.433417
ic1951	3.515647	-53.126194
ic1952	3.557408	-23.712778
ic1953	3.561631	-21.478639
ic1954	3.525386	-51.904833
ic1955	3.523522	-57.241861
ic1956	3.592547	5.067
ic1957	3.537078	-52.456639
ic1958	3.546225	-51.441694
ic1959	3.553497	-50.41425
ic1960	3.542492	-57.206611
ic1961	3.559264	-48.950639
ic1962	3.593747	-21.294056
ic1964	3.558356	-53.173139
ic1965	3.553067	-56.554083
ic1966	3.567608	-51.32225
ic1967	3.629922	3.271028
ic1968	3.577164	-50.651278
ic1969	3.60385	-45.179611
ic1970	3.608756	-43.956833
ic1971	3.599275	-52.65125
ic1972	3.605922	-51.968139
ic1973	3.605839	-51.994167
ic1974	3.611733	-49.550278
ic1975	3.650986	-15.500139
ic1976	3.6191	-47.437917
ic1977	3.6792	17.741167
ic1978	3.618219	-50.150833
ic1979	3.612853	-57.944556
ic1980	3.616386	-57.973861
ic1981,ngc1412	3.674825	-26.86225
ic1982	3.628464	-57.776278
ic1983,ngc1415	3.682461	-22.564472
ic1984	3.663953	-47.075833
ic1986	3.676431	-45.355806
ic1987	3.669797	-55.054806
ic1988	3.712669	-39.887111
ic1989	3.698519	-50.957806
ic1990	3.787175	24.333889
ic1991	3.746331	-51.523417
ic1992	3.752233	-51.004694
ic1993	3.784669	-33.709861
ic1994	3.765292	-51.643333
ic1995	3.838483	25.580778
ic1996	3.752136	-57.324806
ic1997	3.74775	-59.137667
ic1998	3.8587	1.189806
ic1999	3.795233	-56.952083
ic2000	3.818817	-48.858194
ic2001	3.8477	-48.599639
ic2002,ngc1474	3.908431	10.707
ic2003	3.939453	33.874861
ic2004	3.862703	-49.419611
ic2005	3.960983	36.787472
ic2006	3.907903	-35.967139
ic2007,ic2008	3.922989	-28.158333
ic2009	3.893014	-48.989472
ic2010	3.866119	-59.929361
ic2011	3.874208	-57.468417
ic2012	3.882033	-58.651
ic2013	3.945572	-17.1095
ic2014	3.922689	-56.746306
ic2015	3.969839	-40.389139
ic2016	4.033297	20.240444
ic2017	3.944269	-59.39475
ic2018	3.965147	-52.781111
ic2019	4.031569	5.639444
ic2020	3.981428	-54.057611
ic2021	3.989981	-52.656722
ic2022	3.977781	-59.043667
ic2023	3.994619	-52.681139
ic2024	4.00115	-53.371
ic2025	4.006439	-53.065611
ic2026,ngc1509	4.065333	-11.179028
ic2027	4.110997	37.11575
ic2028	4.021731	-52.707444
ic2029	4.021653	-52.800778
ic2030	4.082303	-19.231472
ic2031	4.104089	-5.651889
ic2032	4.117511	-55.323833
ic2033	4.120672	-53.680917
ic2034	4.110231	-57.961389
ic2035	4.150519	-45.517528
ic2036	4.165306	-39.688694
ic2037	4.138611	-58.751167
ic2038	4.148264	-55.989556
ic2039	4.150658	-56.011694
ic2040	4.216603	-32.553278
ic2041,ic2048	4.209694	-32.817361
ic2042	4.19535	-47.270083
ic2043	4.185958	-53.686639
ic2044	4.187214	-54.532556
ic2045	4.243336	-13.174917
ic2046	4.19015	-54.673194
ic2047,ngc1538	4.248911	-13.191722
ic2049	4.201189	-58.557
ic2050	4.232258	-53.475361
ic2051	3.866897	-83.830694
ic2052	4.249589	-54.336194
ic2053	4.26545	-49.358333
ic2054	4.123983	-78.253306
ic2055	4.296811	-48.924111
ic2056	4.273483	-60.206806
ic2057	4.365581	4.048639
ic2058	4.298431	-55.932889
ic2059	4.340639	-31.724583
ic2060	4.298156	-56.61625
ic2061	4.400036	21.083194
ic2062	4.53385	71.919861
ic2063	4.377867	-15.6605
ic2064	4.390761	-15.685167
ic2065	4.357772	-55.933306
ic2066	4.392314	-54.733389
ic2067	4.514175	35.446167
ic2068	4.443578	-42.093722
ic2069	4.432261	-48.208056
ic2070	4.409914	-57.980889
ic2071	4.436997	-53.152111
ic2072	4.4485	-48.3775
ic2073	4.442733	-53.187333
ic2074	4.523064	7.702611
ic2075,ngc1594	4.514331	-5.798278
ic2076	4.468836	-48.228861
ic2077,ngc1593,ngc1608	4.535033	0.567361
ic2078	4.531172	-4.698694
ic2079	4.475228	-53.737917
ic2080	4.531153	-5.756833
ic2081	4.483583	-53.613694
ic2082	4.485444	-53.827222
ic2083	4.512297	-53.980833
ic2084	4.535047	-48.288306
ic2085	4.5234	-54.416833
ic2086	4.525603	-53.647639
ic2087,lbn813	4.666658	25.742222
ic2088	4.517933	26.607028
ic2089	4.547344	-75.539444
ic2090	4.745575	-33.994083
ic2091	4.777561	-4.671806
ic2092	4.779894	-4.943361
ic2093	4.7923	-2.709028
ic2094	4.806897	-5.352639
ic2095	4.812675	-5.124806
ic2096	4.828017	-4.978639
ic2097	4.840061	-5.081222
ic2098	4.845642	-5.418667
ic2099,ngc1677	4.847797	-4.892722
ic2100	4.85415	-4.830917
ic2101	4.861733	-6.231444
ic2102	4.865367	-4.951611
ic2103	4.663347	-76.836806
ic2104	4.9386	-15.797889
ic2105	4.824072	-69.200917
ic2106	4.942747	-28.503917
ic2107,ngc1707	4.972392	8.238361
ic2108,ngc1710	4.954742	-15.289
ic2109	4.983106	-0.305306
ic2110	4.983833	-0.302639
ic2111	4.864478	-69.392167
ic2112	5.008375	4.386528
ic2113,ngc1730	4.992175	-15.823639
ic2114,ngc1748	4.907214	-69.184111
ic2115	4.952422	-66.390194
ic2116	4.954517	-66.389028
ic2117	4.954225	-68.441472
ic2118,lbn959,ngc1909,thewitchheadnebula	5.082067	-7.265639
ic2119	5.114153	-20.345194
ic2120	5.319528	38.185
ic2122	5.317056	-37.089389
ic2125	5.407811	-27.016056
ic2126,ngc1935	5.366308	-67.957389
ic2127,ngc1936	5.370544	-67.978306
ic2128	5.378936	-68.061083
ic2129,ic2130	5.530686	-23.145056
ic2132	5.541297	-13.927111
ic2133,ngc1961	5.701292	69.378444
ic2134	5.384956	-75.446833
ic2135,ic2136	5.553583	-36.398833
ic2137,ic2138	5.572689	-23.533333
ic2139	5.587842	-17.933667
ic2140	5.556086	-75.375361
ic2141	5.706206	-51.032861
ic2142	5.552544	-78.019417
ic2143	5.781281	-18.726389
ic2144	5.837192	23.872417
ic2145	5.673542	-69.670306
ic2146	5.629703	-74.783194
ic2147	5.724461	-30.495028
ic2148	5.653294	-75.562444
ic2149	5.939969	46.104778
ic2150	5.855156	-38.320472
ic2151	5.876786	-17.787278
ic2152	5.964836	-23.180778
ic2153	6.001439	-33.91975
ic2154,ngc2139	6.018836	-23.672639
ic2155	6.010675	-33.997333
ic2156	6.081225	24.158444
ic2157	6.079883	24.071028
ic2158	6.088322	-27.856972
ic2159	6.166006	20.431389
ic2160	5.9246	-76.92025
ic2161	5.956906	-75.139472
ic2162,lbn859	6.217972	17.980083
ic2163	6.274439	-21.375861
ic2164	6.114517	-75.364694
ic2165	6.361861	-12.987222
ic2166	6.448789	59.080083
ic2168	6.563256	44.685472
ic2170	6.568031	44.688444
ic2171	6.741025	-17.932472
ic2172,ngc2282	6.780992	1.316
ic2173	6.846433	33.458056
ic2174	7.151558	75.353028
ic2175	7.14435	35.28825
ic2176	7.125508	32.46975
ic2177,lbn1027	7.076919	-10.471056
ic2178	7.127128	32.512389
ic2179	7.258975	64.926194
ic2180	7.188772	26.371528
ic2181	7.219542	18.995833
ic2182	7.236397	18.945028
ic2183	7.2823	-20.410472
ic2184	7.490389	72.128889
ic2185	7.387789	32.495333
ic2186	7.379939	21.52925
ic2187	7.378697	21.483361
ic2188	7.378661	21.513028
ic2189	7.415997	8.920694
ic2190	7.498417	37.45175
ic2191	7.50485	24.327722
ic2192	7.555642	31.361389
ic2193	7.556586	31.483556
ic2194	7.561164	31.334417
ic2195	7.474342	-51.257417
ic2196	7.569372	31.405667
ic2197	7.573697	31.422
ic2198	7.569758	23.966333
ic2199	7.58215	31.27625
ic2200	7.471531	-62.352917
ic2201	7.604669	33.122722
ic2202	7.465206	-67.574222
ic2203	7.676003	34.230056
ic2204	7.688361	34.232167
ic2205	7.781825	26.872333
ic2206	7.763997	-34.330167
ic2207	7.830803	33.962278
ic2208	7.868844	27.483917
ic2209	7.937281	60.304083
ic2210	7.949025	56.682333
ic2211	7.962683	32.558111
ic2212	7.982556	32.61225
ic2213	7.985153	27.464
ic2214	7.998281	33.290528
ic2215	7.992542	24.928972
ic2216	7.990986	5.6145
ic2217	8.013814	27.500306
ic2218	8.027358	24.432444
ic2219	8.043481	27.4375
ic2220,tobyjugnebula	7.947486	-59.125778
ic2221	8.085542	37.450639
ic2222	8.087436	37.472583
ic2223,ic2224	8.097308	37.460056
ic2225	8.091144	35.946694
ic2226	8.103117	12.5435
ic2227	8.118661	36.233472
ic2228	8.118236	8.025361
ic2230	8.182375	25.684694
ic2231	8.183778	5.087333
ic2232,ngc2543	8.216089	36.254639
ic2233	8.233031	45.742139
ic2234	8.231006	35.492917
ic2235	8.226064	24.076778
ic2236	8.227089	24.048806
ic2237	8.235581	24.679306
ic2238	8.235725	24.661889
ic2239	8.235219	23.866361
ic2240	8.246522	24.467556
ic2241	8.2524	24.129389
ic2242	8.253183	24.132944
ic2243	8.255119	23.962278
ic2244	8.256186	24.545833
ic2245	8.257894	24.536056
ic2246	8.266886	23.84975
ic2247	8.266417	23.199611
ic2248	8.268003	23.134028
ic2249	8.276231	24.493722
ic2250	8.2756	23.632972
ic2251	8.277442	23.949639
ic2252	8.278319	24.693889
ic2253	8.276078	21.409889
ic2254	8.279308	24.780222
ic2255	8.278661	23.457111
ic2256	8.281786	24.176833
ic2257	8.286336	23.649917
ic2258	8.2879	23.577528
ic2259	8.288375	23.565639
ic2260	8.290994	24.67325
ic2261	8.29245	23.512333
ic2262	8.2896	18.4545
ic2263	8.2947	23.580111
ic2264	8.295814	23.71475
ic2265	8.297286	24.193528
ic2266	8.294014	18.410361
ic2267	8.300447	24.735333
ic2268	8.301822	24.796444
ic2269	8.302433	23.047583
ic2270	8.300103	19.097667
ic2271	8.305472	24.526917
ic2272	8.301992	18.735889
ic2273	8.303561	18.401667
ic2274	8.303892	18.665833
ic2275	8.303811	18.411444
ic2276	8.308158	18.477722
ic2277	8.309011	18.650056
ic2278	8.309569	18.461528
ic2279	8.309867	18.567944
ic2280	8.3107	18.44975
ic2281	8.315042	18.909111
ic2282	8.320981	24.792639
ic2283	8.321536	24.786417
ic2284	8.3163	18.605583
ic2285	8.317447	18.914667
ic2286	8.317803	18.956111
ic2287	8.318786	19.400472
ic2288	8.322883	23.747306
ic2289	8.318789	18.498278
ic2290	8.321072	19.31325
ic2291	8.321708	18.508389
ic2292	8.322775	19.563583
ic2293	8.325586	21.394306
ic2294	8.3239	18.984694
ic2295	8.324164	18.414222
ic2296	8.324597	18.89875
ic2297	8.334617	18.381972
ic2298	8.3353	18.403111
ic2299	8.335947	19.337444
ic2300	8.336833	18.420056
ic2301	8.337203	18.43375
ic2302	8.338133	19.357222
ic2303	8.338686	19.419
ic2304	8.343247	19.439528
ic2305	8.344467	19.452917
ic2306	8.344278	19.110278
ic2307	8.345228	19.440667
ic2308	8.345903	19.362278
ic2309	8.345447	18.397833
ic2310	8.3462	18.4635
ic2311	8.312772	-25.36975
ic2312	8.348161	18.510889
ic2313	8.348494	18.514194
ic2314	8.351011	18.762667
ic2315	8.352969	18.91525
ic2316	8.354222	19.759417
ic2317	8.355961	18.844333
ic2318	8.3591	18.622889
ic2319	8.359183	18.476722
ic2320	8.359833	18.67025
ic2321	8.360881	18.469139
ic2322	8.360828	18.484111
ic2323	8.36145	18.61325
ic2324	8.366314	19.194028
ic2325	8.369092	18.912139
ic2326	8.370039	19.012083
ic2327	8.357769	3.169278
ic2328	8.371494	19.616444
ic2329	8.372078	19.415972
ic2330	8.373094	18.853611
ic2331	8.376431	19.679667
ic2332	8.377675	19.923056
ic2333	8.383569	19.081861
ic2334	8.383325	18.613778
ic2335	8.385289	19.408028
ic2336	8.388622	18.537444
ic2337	8.388969	18.535222
ic2338	8.392408	21.338083
ic2339	8.392836	21.347639
ic2340	8.391681	18.749444
ic2341	8.394844	21.434889
ic2342	8.39225	18.579611
ic2343	8.398314	19.025639
ic2344	8.398539	18.659722
ic2345	8.402344	19.952167
ic2346	8.403028	19.706222
ic2347	8.403911	18.773861
ic2348	8.405625	20.53325
ic2349	8.404642	19.008056
ic2350	8.407883	19.552056
ic2351	8.408389	18.588778
ic2352	8.411106	19.602778
ic2353	8.410472	18.656556
ic2354	8.411322	18.666444
ic2355	8.414392	20.463472
ic2356	8.416906	19.497556
ic2357	8.417933	19.508861
ic2358	8.418083	19.495194
ic2359,ngc2582	8.420019	20.33475
ic2360	8.420858	19.516444
ic2361	8.429028	27.874583
ic2362	8.428172	19.942222
ic2363	8.429283	19.449278
ic2364	8.430969	19.759722
ic2365,ic2366	8.43835	27.840139
ic2367	8.4028	-18.775556
ic2368	8.433692	19.883
ic2369	8.437794	20.23225
ic2370	8.439672	19.638056
ic2371	8.443606	19.798583
ic2372	8.444617	19.883083
ic2373	8.446939	20.364833
ic2374	8.472817	30.443194
ic2375	8.438797	-13.303139
ic2376	8.473925	30.407694
ic2377	8.440578	-13.306167
ic2378	8.475458	30.431333
ic2379	8.441056	-13.292861
ic2380	8.478858	30.404528
ic2381	8.472706	19.791639
ic2382	8.479478	22.053472
ic2383	8.494819	30.687972
ic2384	8.573189	32.434778
ic2385	8.586211	37.265972
ic2386	8.578844	25.806694
ic2387	8.642778	30.798694
ic2388	8.6657	19.645306
ic2389	8.799381	73.539194
ic2390,ngc2643	8.697706	19.702528
ic2391,omivelcluster	8.675522	-53.035472
ic2392	8.741889	18.286139
ic2393	8.780331	28.171306
ic2394	8.785253	28.236556
ic2395	8.708364	-48.150556
ic2396	8.777942	17.649194
ic2397	8.778294	17.659778
ic2398	8.779047	17.754917
ic2399	8.797147	18.911889
ic2400	8.799764	38.069806
ic2401	8.802861	37.755361
ic2402	8.799733	31.785639
ic2403	8.769258	-15.357
ic2404	8.802903	29.491361
ic2405	8.811878	37.218639
ic2406	8.801281	17.702389
ic2407	8.802542	17.611472
ic2408	8.805622	19.037417
ic2409	8.80685	18.331139
ic2410,ngc2667	8.807569	19.0195
ic2411,ngc2667b	8.808381	19.043889
ic2412	8.823253	18.543167
ic2413	8.825436	18.74475
ic2414	8.830589	18.792417
ic2415	8.833864	18.651611
ic2416	8.842264	18.559611
ic2417	8.852267	18.624917
ic2418	8.856967	17.94525
ic2419	8.869278	18.101361
ic2420	8.859378	3.100694
ic2421	8.906	32.680861
ic2422	8.906753	20.224806
ic2423	8.913078	20.220278
ic2424,ngc2704	8.946581	39.382194
ic2425	8.930592	-3.423139
ic2426	8.975133	2.9255
ic2427	9.017139	37.875444
ic2428	9.054083	30.591333
ic2429	9.061814	29.296
ic2430	9.073008	27.953
ic2431	9.076486	14.594083
ic2432	9.07765	5.512056
ic2433	9.091314	22.602222
ic2434	9.121128	37.215278
ic2435	9.113831	26.275444
ic2436	9.089922	-19.165472
ic2437	9.092531	-19.207111
ic2438	9.235786	73.417361
ic2439	9.144017	32.592944
ic2440	9.263933	73.459056
ic2441	9.167306	22.853333
ic2442	9.168103	22.838333
ic2443	9.191914	28.826583
ic2444	9.214128	30.212278
ic2445	9.220167	31.807861
ic2446,ic2447	9.225383	28.95175
ic2448	9.118406	-69.941833
ic2449,ngc2783b	9.225875	30.000139
ic2450	9.2848	25.429167
ic2451	9.263272	23.496417
ic2452	9.265994	23.47225
ic2453	9.265147	20.928889
ic2454	9.267158	17.820694
ic2455,ngc2804	9.280558	20.1985
ic2456	9.290067	34.674389
ic2457	9.284483	20.0935
ic2458	9.358353	64.238694
ic2459	9.316519	34.862194
ic2460,ngc2827	9.321947	33.880806
ic2461	9.332786	37.19125
ic2462	9.382292	22.686361
ic2463	9.383403	22.618556
ic2464	9.389519	22.63025
ic2465	9.392086	24.445694
ic2466	9.395842	24.518444
ic2467	9.414644	38.35175
ic2468	9.417081	38.344028
ic2469	9.383628	-32.44975
ic2470	9.428144	23.361611
ic2471	9.420047	-6.829917
ic2472	9.4427	21.385028
ic2473	9.456528	30.440806
ic2474	9.453169	23.034278
ic2475	9.465092	29.791861
ic2476	9.464675	29.98575
ic2477,ic2480	9.471619	29.706056
ic2478	9.466925	30.036972
ic2479	9.467803	29.991444
ic2481	9.458003	3.929611
ic2482	9.449783	-12.108917
ic2483	9.490497	30.994722
ic2484	9.4473	-42.842806
ic2485	9.4533	-39.284722
ic2486	9.504825	26.641278
ic2487	9.502547	20.090861
ic2488	9.460619	-57.006944
ic2489	9.519897	-5.884167
ic2490	9.551014	29.928361
ic2491	9.587283	34.731667
ic2492	9.554131	-37.866333
ic2493	9.604872	37.364
ic2495	9.635386	28.057667
ic2496	9.645694	34.726778
ic2497	9.684469	34.732722
ic2498	9.689428	28.114472
ic2499	9.690175	27.89525
ic2500	9.706492	36.349694
ic2501	9.646439	-60.091861
ic2502	9.720944	35.160528
ic2503	9.721067	35.206222
ic2504	9.642728	-69.085111
ic2505	9.751931	27.268583
ic2506	9.753547	27.252
ic2507	9.74275	-31.79
ic2508	9.7853	33.508056
ic2509	9.7822	5.701944
ic2510	9.795411	-32.837444
ic2511,ic2512	9.823486	-32.839194
ic2513,ic2514	9.833553	-32.882833
ic2515	9.91095	37.408583
ic2516	9.913433	37.686944
ic2517	9.880742	-33.741944
ic2518	9.932925	37.155528
ic2519	9.933003	34.036583
ic2520	9.938922	27.227583
ic2521	9.954375	33.976306
ic2522	9.919156	-33.137139
ic2523	9.919311	-33.210222
ic2524	9.959128	33.619722
ic2525	9.9736	37.101861
ic2526	9.950842	-32.256861
ic2527	10.001803	38.172194
ic2528,ngc3084	9.985117	-27.128806
ic2529,ngc3081	9.991539	-22.826278
ic2530	10.025294	37.203944
ic2531	9.998825	-29.616972
ic2532	10.0015	-34.228278
ic2533	10.008797	-31.245
ic2534	10.024961	-34.112417
ic2535	10.075508	38.006028
ic2536	10.058394	-33.94975
ic2537	10.064414	-27.570861
ic2538	10.065692	-34.807528
ic2539	10.071169	-31.362944
ic2540	10.112975	31.475722
ic2541	10.096669	-17.434556
ic2542	10.130706	34.315306
ic2543	10.139944	37.842778
ic2544	10.141592	33.346389
ic2545	10.109739	-33.858278
ic2546	10.118311	-33.261361
ic2547	10.167914	36.502444
ic2548	10.131931	-35.229611
ic2549	10.169489	36.464861
ic2550	10.174422	27.956111
ic2551	10.177867	24.414139
ic2552	10.179483	-34.844694
ic2553	10.155797	-62.613694
ic2554	10.147378	-67.030861
ic2555,ngc3157	10.195119	-31.642861
ic2556	10.210453	-34.728861
ic2557	10.268297	38.109222
ic2558	10.245594	-34.338722
ic2559	10.245942	-34.058806
ic2560	10.271867	-33.563806
ic2561	10.319058	34.675028
ic2562	10.315139	16.155528
ic2563	10.314425	-32.596556
ic2564	10.357694	36.452056
ic2565	10.354964	27.930083
ic2566	10.372053	36.583028
ic2567	10.366056	24.655222
ic2568	10.375003	36.599306
ic2569	10.381553	24.606417
ic2570	10.359528	-33.623222
ic2571,ngc3223	10.359744	-34.266806
ic2572	10.418689	28.094806
ic2573	10.391717	-35.455583
coddingtonsnebula,ic2574	10.473189	68.412139
ic2575	10.423333	-32.63625
ic2576	10.43305	-32.903472
ic2577	10.467069	32.763889
ic2578	10.456303	-33.877333
ic2579,ngc3251	10.488011	26.09925
ic2580	10.471661	-31.518028
ic2581	10.458097	-57.617306
ic2582	10.486389	-30.3425
ic2583	10.519567	26.055056
ic2584	10.497636	-34.911639
ic2585,ngc3271	10.507358	-35.3595
ic2586	10.517333	-28.716639
ic2587	10.516556	-34.562944
ic2588	10.530594	-30.384528
ic2589	10.539117	-24.037556
ic2590	10.604606	26.962472
ic2591	10.610742	35.052917
ic2592,ngc3366	10.585633	-43.691806
ic2593	10.604431	-12.725806
ic2594	10.601158	-24.323083
ic2595	10.625867	-11.116722
ic2596	10.570128	-73.240139
ic2597	10.629847	-27.081694
ic2598	10.661758	26.727556
ic2599	10.624192	-58.733389
ic2600	10.777444	72.320444
ic2601	10.787033	72.323028
ic2602,tetcarcluster	10.715964	-64.394194
ic2603	10.807044	32.927306
ic2604	10.823631	32.772722
ic2605	10.829872	32.973194
ic2606	10.838236	37.956222
ic2607	10.838594	37.993944
ic2608	10.837644	32.768167
ic2609,ngc3404	10.838328	-12.108722
ic2610	10.868908	33.083167
ic2611	10.877481	10.136361
ic2612	10.893656	32.767639
ic2613,ngc3395	10.830586	32.982861
ic2614	11.026056	38.803667
ic2615	11.033967	37.94525
ic2616	11.034933	38.78725
ic2617	11.035453	38.66425
ic2618	11.033006	27.78925
ic2619	11.037572	37.966083
ic2620	11.039986	38.505028
ic2621	11.005553	-65.249361
ic2622,ngc3505,ngc3508	11.049908	-16.289444
ic2623	11.064156	-20.093056
ic2624,ngc3497,ngc3525,ngc3528	11.121686	-19.471556
ic2625,ngc3529	11.121978	-19.555639
ic2626	11.151075	26.904167
ic2627	11.164831	-23.725944
ic2628	11.193853	12.121972
ic2629	11.210261	12.104944
ic2630	11.211997	12.318944
ic2631	11.164664	-76.614306
ic2632	11.218317	11.673278
ic2633	11.219456	11.601
ic2634	11.224514	10.485972
ic2635	11.224947	11.463889
ic2636	11.226122	11.456167
ic2637	11.230486	9.586306
ic2638	11.231086	10.563389
ic2639	11.232094	9.642806
ic2640	11.234858	10.997667
ic2641	11.236264	9.399333
ic2642	11.237722	12.265667
ic2643	11.240711	10.126222
ic2644	11.241614	10.768472
ic2645	11.241894	11.886778
ic2646	11.243778	12.5285
ic2647	11.244061	12.142
ic2648	11.246008	10.224833
ic2649	11.246236	11.127694
ic2650	11.247961	13.852472
ic2651	11.247856	12.239778
ic2652	11.247867	12.448056
ic2653	11.248286	10.548361
ic2654	11.250794	12.499472
ic2655	11.251433	12.164389
ic2656	11.251494	12.379139
ic2657	11.252419	13.694722
ic2658	11.252431	12.996611
ic2659	11.257733	12.887667
ic2660	11.2579	12.437194
ic2661	11.258103	13.608667
ic2662	11.258553	12.771056
ic2663	11.258994	12.603917
ic2664	11.260678	12.562694
ic2665	11.261328	11.724139
ic2666	11.262158	13.78225
ic2667	11.262233	12.116833
ic2668	11.258967	-14.171083
ic2669	11.264783	13.429556
ic2670	11.266544	11.783361
ic2671	11.267589	13.12425
ic2672	11.267728	10.157278
ic2673	11.267814	10.162556
ic2674	11.268958	11.048639
ic2675	11.269669	12.249306
ic2676	11.271808	9.821833
ic2677	11.272028	12.215861
ic2678	11.272678	11.949111
ic2679	11.273111	12.015389
ic2680	11.273758	9.807139
ic2681	11.275903	11.207194
ic2682	11.2767	9.410778
ic2683	11.28175	12.099278
ic2684	11.283625	13.099639
ic2685	11.283358	10.094083
ic2686	11.284031	12.951667
ic2687	11.286661	10.158111
ic2689	11.28875	12.959944
ic2690	11.289331	12.975417
ic2691	11.290161	12.031083
ic2692	11.292561	10.768056
ic2693	11.293419	13.548833
ic2694	11.294056	13.376111
ic2695	11.296825	13.727667
ic2696	11.296925	12.75575
ic2697	11.297536	13.399972
ic2698	11.297506	11.885778
ic2699	11.297958	11.909222
ic2700	11.298383	12.054194
ic2701	11.299172	11.118056
ic2702	11.299231	9.412472
ic2703	11.301425	17.649528
ic2704	11.301114	12.454194
ic2705	11.301022	11.904083
ic2706	11.308111	12.548444
ic2707	11.308567	9.474861
ic2708	11.309614	12.711111
ic2709	11.311711	12.561694
ic2710	11.312311	13.566583
ic2711	11.312914	13.738444
ic2712	11.314661	9.626889
ic2713	11.319506	12.164806
ic2714	11.290931	-62.725111
ic2715	11.320664	11.952167
ic2716	11.321206	11.698556
ic2717	11.321881	12.048556
ic2718	11.322472	12.022278
ic2719	11.325611	12.059778
ic2720	11.326569	12.076583
ic2721	11.328558	12.310639
ic2722	11.328989	13.962917
ic2723	11.329972	12.033444
ic2724	11.330122	10.716556
ic2725	11.332622	13.429278
ic2726	11.3329	13.415583
ic2727	11.333353	12.033333
ic2728	11.334758	13.427
ic2729	11.335214	13.409306
ic2730	11.335386	12.366528
ic2731	11.336186	13.558278
ic2732	11.336772	12.404028
ic2733	11.338142	13.83525
ic2734	11.33995	12.443028
ic2735	11.351083	34.343944
ic2736	11.348506	12.408667
ic2737	11.352292	14.293194
ic2738	11.356406	34.356667
ic2739	11.353453	11.91475
ic2740	11.354739	8.752306
ic2741	11.354853	9.152361
ic2742	11.355203	10.446722
ic2743	11.356942	8.693111
ic2744	11.361808	34.362806
ic2745	11.358822	13.426611
ic2746	11.360117	11.737083
ic2747	11.361156	8.80325
ic2748	11.362233	8.804972
ic2749	11.362556	8.574778
ic2750	11.364108	9.658444
ic2751	11.368719	34.366361
ic2752	11.367206	14.1245
ic2753	11.366586	9.878056
ic2754	11.367328	14.144056
ic2755	11.367336	13.793111
ic2756	11.366919	9.960167
ic2757	11.36725	8.393833
ic2758	11.367592	7.813528
ic2759	11.370356	24.317167
ic2760	11.370222	12.665417
ic2761	11.371436	14.177583
ic2762	11.371644	12.722528
ic2763	11.371822	13.065056
ic2764	11.451397	-28.980222
ic2765	11.373089	14.199056
ic2766	11.373072	12.903472
ic2767	11.373108	13.077806
ic2768	11.373211	12.528917
ic2769	11.373792	14.195889
ic2770	11.373544	9.220667
ic2771	11.374458	12.519167
ic2772	11.375111	13.599139
ic2773	11.376475	13.574528
ic2774	11.376986	12.514944
ic2775	11.377656	12.512
ic2776	11.377775	13.330528
ic2777	11.377931	12.025583
ic2778	11.378314	12.526306
ic2779	11.379031	13.345306
ic2780	11.380036	10.149556
ic2781	11.380742	12.344889
ic2782	11.382044	13.441278
ic2783	11.381564	8.884056
ic2784	11.386564	13.117722
ic2785	11.3876	13.39125
ic2786	11.388194	13.392
ic2787	11.388633	13.629778
ic2788	11.390825	12.698028
ic2789	11.392406	14.188028
ic2790	11.392794	9.555361
ic2791	11.393783	12.895778
ic2792	11.394864	11.404833
ic2793	11.396497	9.449778
ic2794	11.401014	12.790972
ic2795	11.401131	12.135111
ic2796	11.402319	9.344139
ic2797	11.40585	11.705944
ic2798	11.406664	12.415611
ic2799	11.407408	13.849111
ic2800	11.407522	12.208806
ic2801	11.408064	10.183833
ic2802	11.408433	12.20875
ic2803	11.409836	9.850028
ic2804	11.415481	13.222056
ic2805	11.416636	14.014472
ic2806	11.420917	9.652222
ic2807	11.421403	11.530056
ic2808	11.424133	9.132056
ic2809	11.427158	8.526278
ic2810	11.429181	14.676583
ic2811	11.429069	9.170528
ic2812	11.432172	11.529917
ic2813	11.435139	11.25575
ic2814	11.435697	9.661806
ic2815	11.437931	12.803833
ic2816	11.438411	10.6365
ic2817	11.438558	9.149
ic2818	11.440797	12.920944
ic2819	11.440956	13.844889
ic2820	11.440792	10.238472
ic2821	11.443022	13.962917
ic2822	11.442792	11.440083
ic2823	11.445742	12.848417
ic2824	11.451353	14.085278
ic2825	11.450989	8.443917
ic2826	11.451689	13.238722
ic2827	11.452686	11.514389
ic2828	11.453039	8.731056
ic2829	11.454161	10.322361
ic2830	11.455994	7.814306
ic2831	11.456281	8.978917
ic2832	11.456978	13.989444
ic2833	11.457253	13.602806
ic2834	11.458839	13.570333
ic2835	11.458775	12.142889
ic2836	11.460336	9.084806
ic2837	11.461656	10.313056
ic2838	11.462567	14.01125
ic2839	11.462617	10.81975
ic2840	11.463222	13.425889
ic2841	11.463572	12.603111
ic2842	11.463247	9.651972
ic2843	11.466136	13.183917
ic2844	11.466139	11.453278
ic2845	11.466794	12.52975
ic2846	11.466803	11.158278
ic2847	11.467608	13.930389
ic2848	11.470464	13.030472
ic2849	11.469906	9.094
ic2850	11.470267	9.06225
ic2851	11.470725	11.394389
ic2852	11.470569	9.800472
ic2853	11.470794	9.147028
ic2854	11.472186	8.968722
ic2855	11.473608	9.68775
ic2856	11.471197	-12.890694
ic2857	11.475289	9.104417
ic2858	11.476656	13.6615
ic2859	11.478267	9.1085
ic2860	11.479056	14.041889
ic2861	11.483047	38.851278
ic2862	11.4787	10.127278
ic2863	11.481661	9.095306
ic2864	11.483242	12.367722
ic2865	11.483264	9.1155
ic2866	11.483342	9.042194
ic2867	11.483483	9.089389
ic2868	11.484944	9.094306
ic2869	11.485756	9.017389
ic2870	11.486783	11.8655
ic2871	11.489081	8.602361
ic2872	11.468897	-62.988944
ic2873	11.490953	13.218306
ic2874	11.490986	10.629167
ic2875	11.493036	12.989889
ic2876	11.492667	9.016167
ic2877	11.493817	12.853278
ic2878	11.493947	9.967583
ic2879	11.495636	9.013861
ic2880	11.498061	13.198833
ic2881	11.498447	12.511222
ic2882	11.502622	11.989139
ic2883	11.504386	10.910917
ic2884	11.461403	-79.734389
ic2885	11.506281	9.772056
ic2886	11.506789	11.562667
ic2887,ngc3705a	11.508256	9.387944
ic2888	11.509753	9.9085
ic2889	11.508053	-13.091
ic2890	11.512819	13.181833
ic2891	11.513372	12.677722
ic2892	11.513586	10.588556
ic2893	11.5148	13.391028
ic2894	11.515972	13.235361
ic2895	11.515914	9.976861
ic2896	11.520397	12.350056
ic2897	11.522047	11.549056
ic2898	11.522336	13.336222
ic2899	11.522325	10.634722
ic2900	11.524914	13.167306
ic2901	11.525592	12.699722
ic2902	11.525878	14.22275
ic2903	11.527989	12.642583
ic2904	11.528436	13.184139
ic2905	11.529717	9.106972
ic2906	11.530447	13.132889
ic2907	11.530208	9.899444
ic2908	11.530689	12.937889
ic2909	11.530803	11.470222
ic2910	11.531864	-9.725361
ic2911	11.534619	12.977361
ic2912	11.535308	11.70975
ic2913	11.530931	-30.410778
ic2914	11.536786	13.492472
ic2916	11.537819	11.683722
ic2917	11.538703	10.945444
ic2918	11.540619	13.2485
ic2919	11.543028	14.189222
ic2920	11.546853	12.557111
ic2921	11.547022	10.296472
ic2922	11.547561	12.922833
ic2923	11.548208	13.163972
ic2924	11.547831	9.023278
ic2925	11.553675	34.265111
ic2926	11.551131	12.436444
ic2927	11.551325	13.085722
ic2928	11.558322	34.31625
ic2929	11.558742	12.137333
ic2930	11.562261	10.088667
ic2931	11.564025	12.467222
ic2932	11.564919	10.543389
ic2933	11.570208	34.3125
ic2934	11.572097	13.322
ic2935	11.580058	10.250139
ic2936	11.58245	13.008806
ic2937	11.584269	10.103361
ic2938	11.593417	13.680722
ic2939	11.593883	10.697083
ic2940	11.600761	21.961667
ic2941	11.602769	10.055583
ic2942	11.603392	11.815889
ic2943	11.611753	54.846028
ic2944,lamcennebula	11.596369	-63.019833
ic2945	11.617858	12.926583
ic2946	11.624914	32.252472
ic2947	11.625269	31.362333
ic2948	11.65165	-63.443861
ic2949	11.681764	-46.454583
ic2950	11.693867	37.992111
ic2951	11.723489	19.749806
ic2952	11.738092	33.351361
ic2953,ngc3855	11.740494	33.355083
ic2954	11.750906	26.7865
ic2955	11.751086	19.620611
ic2956	11.754878	26.767389
ic2957	11.760261	31.299556
ic2958	11.761756	33.154444
ic2959,ngc3871	11.769483	33.10875
ic2960	11.772139	35.00375
ic2961	11.797103	31.34475
ic2962	11.818331	-12.311361
ic2963,ngc3915	11.823481	-5.118444
ic2964	11.831242	12.050306
ic2965,ngc3957	11.900419	-19.568889
ic2966	11.837097	-64.872944
ic2967	11.848647	30.850694
ic2968	11.875147	20.625472
ic2969	11.875353	-3.87225
ic2970	11.886042	-23.123278
ic2971	11.890983	30.696917
ic2972,ngc3952	11.894619	-3.996528
ic2973	11.897433	33.3655
ic2974,ic2975	11.896869	-5.167833
ic2976,ngc3979	11.933625	-2.720861
ic2977	11.920739	-37.696306
ic2978	11.939786	32.038722
ic2979	11.9484	32.158806
ic2980	11.958378	-73.6845
ic2981	11.928506	32.188889
ic2982,ngc4004b	11.964272	27.868667
ic2983	11.971314	-2.110056
ic2984	11.985342	30.696944
ic2985	11.986875	30.731222
ic2986	11.997114	30.844417
ic2987	12.056817	38.813306
ic2988	12.061722	3.42925
ic2989,ngc4139	12.076119	1.801611
ic2990	12.077389	11.050056
ic2991	12.086808	10.640361
ic2992	12.087731	30.855639
ic2993	12.093981	32.822194
ic2994	12.091075	12.702889
ic2995	12.096364	-27.940139
ic2996	12.096842	-29.971917
ic2997	12.095686	20.280861
ic2998	12.098678	20.753361
ic2999	12.099317	31.3485
ic3000	12.102375	-29.673389
ic3001	12.104669	33.525861
ic3002	12.117831	33.382833
ic3003	12.125728	32.813
ic3004	12.119511	13.247528
ic3005	12.120603	-30.024639
ic3006	12.123428	12.993389
ic3007	12.125217	31.348111
ic3008	12.131056	13.577306
ic3009	12.133364	12.646472
ic3010	12.132614	-30.339472
ic3011,ngc4119,ngc4124	12.136006	10.378889
ic3012	12.139983	11.176611
ic3013	12.140439	10.016667
ic3014	12.143611	38.831778
ic3015	12.150078	-31.519889
ic3016	12.15515	11.430222
ic3017	12.156342	13.618167
ic3018	12.156933	13.574444
ic3019	12.156183	13.992417
ic3020	12.157561	14.2245
ic3021	12.165158	13.049972
ic3022	12.167328	38.739972
ic3023	12.167153	14.366861
ic3024	12.169981	12.325667
ic3025	12.173081	10.188556
ic3026	12.176194	-29.923222
ic3027	12.175019	14.193528
ic3028	12.176581	11.760806
ic3029	12.178294	13.331278
ic3030	12.185008	14.143556
ic3031	12.184494	13.308444
ic3032	12.185489	14.274806
ic3033	12.186097	13.5875
ic3034	12.196611	14.201139
ic3035,ngc4165	12.203278	13.246528
ic3036	12.204197	12.488389
ic3037	12.205689	9.986444
ic3038	12.209058	11.352833
ic3039	12.209047	12.309889
ic3040	12.209592	11.075028
ic3041	12.21185	12.762833
ic3042,ngc4178	12.212903	10.865972
ic3043	12.213106	10.009667
ic3044	12.213478	13.976472
ic3045	12.216575	12.7795
ic3046	12.218853	12.918222
ic3047	12.220731	12.997667
ic3048	12.222622	13.069028
ic3049	12.226028	14.480278
ic3050,ngc4189	12.229797	13.424806
ic3051,ngc4193	12.231553	13.172861
ic3052	12.230075	12.690556
ic3053	12.231092	14.222972
ic3054	12.237342	13.542944
ic3055	12.239528	12.091389
ic3056	12.243594	12.811861
ic3057	12.250742	-44.472972
ic3058	12.246514	14.0955
ic3059	12.248617	13.460528
ic3060	12.250581	12.547111
ic3061	12.251233	14.028972
ic3062	12.251492	13.59475
ic3063	12.251869	12.016722
ic3064,ngc4206	12.254669	13.023972
ic3065	12.253489	14.432889
ic3066	12.254606	13.473139
ic3068	12.256444	11.510889
ic3069	12.255519	10.160806
ic3070	12.256853	13.039472
ic3071	12.25885	9.545556
ic3072	12.260592	9.555639
ic3073	12.259889	13.619167
ic3074	12.262831	10.699194
ic3075	12.265303	23.595556
ic3076	12.267772	9.078944
ic3077	12.26565	14.433028
ic3078	12.266678	12.687306
ic3079	12.267814	11.534861
ic3080	12.267408	14.189389
ic3081	12.269183	12.691306
ic3082	12.270028	23.842083
ic3083	12.272567	12.527778
ic3084	12.273183	23.917889
ic3085	12.273892	9.469
ic3086	12.274372	9.009167
ic3087	12.274028	13.287778
ic3088	12.274544	9.458806
ic3089	12.274917	23.827722
ic3090	12.275447	9.439444
ic3091	12.274769	14.012361
ic3092	12.275636	10.046417
ic3093	12.278433	14.277806
ic3094	12.282225	13.625417
ic3095	12.282094	23.957917
ic3096	12.281211	14.514583
ic3097	12.283642	9.407556
ic3098,ngc4235	12.286078	7.191583
ic3099	12.285908	12.454028
ic3100	12.284875	12.289833
ic3101	12.288792	11.943472
ic3102,ngc4223	12.290503	6.690083
ic3103	12.291236	9.360444
ic3104	12.312794	-79.726056
ic3105	12.292708	12.388111
ic3106	12.296058	9.613139
ic3107	12.296369	10.844639
ic3108	12.295194	13.379917
ic3109	12.295586	13.171028
ic3110	12.295789	37.399694
ic3111	12.297447	8.430278
ic3112	12.296767	26.030722
ic3113,ngc4246	12.299478	7.185917
ic3114	12.299097	9.135389
ic3115,ngc4241	12.299972	6.654194
ic3116	12.299214	25.076528
ic3117	12.301294	9.076528
ic3118	12.303069	9.499806
ic3119	12.302356	24.688306
ic3120	12.304264	13.749139
ic3121	12.304861	13.257222
ic3122	12.30595	25.216806
ic3123	12.307664	8.064917
ic3124	12.307647	9.588389
ic3125	12.307075	24.365111
ic3126	12.310322	13.815167
ic3127	12.309786	11.870417
ic3128	12.311167	11.733611
ic3128a	12.311631	11.731833
ic3128b	12.310711	11.735028
ic3129	12.312489	9.590667
ic3130	12.313778	8.232972
ic3131,ic3132	12.314136	7.861889
ic3133	12.315156	7.639667
ic3134	12.315589	8.961611
ic3135	12.314606	27.4915
ic3136	12.315936	6.184389
ic3137	12.315186	12.470056
ic3138	12.315611	12.443889
ic3139	12.316878	9.126778
ic3140	12.316078	27.129472
ic3141	12.316233	24.186278
ic3142	12.317639	13.981389
ic3143	12.318164	27.298417
ic3144	12.319378	25.296972
ic3145	12.319581	24.294139
ic3146	12.320139	25.715028
ic3147	12.321639	12.017222
ic3148	12.322672	7.870333
ic3149	12.323392	12.301389
ic3150	12.324581	7.798222
ic3151	12.3258	9.414222
ic3152	12.326664	-26.1455
ic3153	12.3269	5.397806
ic3154	12.326108	25.585917
ic3155	12.329253	6.00575
ic3156	12.328928	9.148583
ic3157	12.329978	12.421944
ic3158	12.330517	9.28975
ic3159	12.331447	11.674472
ic3160	12.333292	9.101889
ic3161	12.333669	8.999056
ic3162	12.334203	8.996972
ic3163	12.334931	9.255611
ic3164	12.334692	24.955917
ic3165	12.334658	27.975333
ic3166	12.331667	60.694278
ic3167	12.33855	9.545361
ic3168	12.338483	27.920389
ic3169	12.339275	25.5995
ic3170	12.340708	9.42425
ic3171	12.340017	25.560583
ic3172	12.340153	27.818778
ic3173	12.341717	11.340944
ic3174	12.341536	10.245167
ic3175	12.342597	9.853417
ic3176	12.341689	25.515417
ic3177	12.342869	14.127611
ic3178	12.343072	26.169306
ic3179	12.343814	26.165389
ic3180	12.339928	60.694333
ic3181,ngc4286	12.345025	29.345889
ic3182	12.3466	12.730139
ic3183	12.346908	6.686722
ic3184	12.346333	24.915583
ic3185	12.347967	25.429694
ic3186	12.348856	24.668583
ic3187	12.348522	11.161806
ic3188	12.348639	11.008889
ic3189	12.348978	25.426528
ic3190	12.350669	9.569778
ic3191	12.351431	7.704417
ic3192	12.351336	11.754611
ic3193	12.350356	27.898778
ic3194	12.3525	25.1335
ic3195	12.354842	25.808278
ic3196	12.357397	11.757778
ic3197	12.357194	25.443889
ic3198	12.35865	26.366306
ic3199	12.362667	10.595639
ic3200	12.360331	26.760778
ic3201	12.361214	25.726
ic3202	12.362314	27.057111
ic3203	12.362675	25.884667
ic3204	12.364008	24.249111
ic3205	12.36415	26.341
ic3206	12.364253	26.363583
ic3207	12.364508	24.354556
ic3208	12.365439	11.966833
ic3209	12.368375	11.754722
ic3210	12.366939	28.431083
ic3211,ngc4307a	12.3687	8.990556
ic3212	12.367611	28.186
ic3213	12.368797	23.869611
ic3214	12.369197	27.235083
ic3215	12.36955	26.051944
ic3216	12.369947	25.286694
ic3217	12.370297	26.388028
ic3218	12.372089	6.927917
ic3219	12.370842	25.951333
ic3220	12.372664	10.601972
ic3221	12.372264	25.283778
ic3222	12.372075	28.831583
ic3223	12.375169	9.48725
ic3224	12.376642	12.158028
ic3225	12.377497	6.677056
ic3226	12.376375	26.067333
ic3227	12.376572	24.085139
ic3228	12.377606	24.330083
ic3229	12.381333	6.679861
ic3230	12.377689	27.746972
ic3231	12.378828	24.820472
ic3232	12.379942	24.424528
ic3233	12.381914	12.566778
ic3234	12.381156	28.112528
ic3235	12.38275	13.545778
ic3236	12.383397	10.101222
ic3237	12.382781	28.494167
ic3238	12.385106	14.458333
ic3239	12.385992	11.726
ic3240	12.385367	10.362278
ic3241	12.385678	26.905278
ic3242	12.386233	26.248889
ic3243	12.386481	27.765694
ic3244	12.386739	14.388972
ic3245	12.388253	9.129556
ic3246	12.388097	13.051833
ic3247	12.387219	28.89375
ic3248	12.388022	25.552028
ic3249	12.388314	25.444667
ic3250	12.388283	25.628806
ic3251	12.388581	25.653389
ic3252	12.390256	28.618222
ic3253	12.395894	-34.622194
ic3254,ngc4336	12.391619	19.426917
ic3255	12.392983	9.648611
ic3256,ngc4342	12.394167	7.054
ic3257	12.395753	7.253778
ic3258	12.395686	12.478333
ic3259	12.396811	7.186833
ic3260,ngc4341	12.398211	7.107111
ic3261	12.397917	11.481306
ic3262	12.396714	27.394278
ic3263	12.397386	28.1995
ic3264	12.397764	25.557389
ic3265	12.399675	7.803778
ic3266,ngc4353	12.400072	7.785194
ic3267	12.401536	7.041278
ic3268	12.402067	6.607472
ic3269	12.401222	27.434778
ic3270	12.401625	27.577889
ic3271	12.403869	7.952972
ic3272	12.402586	23.284639
ic3273,ngc4356	12.404036	8.535861
ic3274,ngc4360b	12.404089	9.266861
ic3275	12.405411	10.446333
ic3276	12.403917	25.818778
ic3277	12.404364	25.564
ic3278	12.404156	27.420806
ic3279	12.406675	12.852444
ic3280	12.407428	13.233444
ic3281	12.407753	7.819139
ic3282	12.407792	25.670639
ic3283	12.407783	27.21125
ic3284	12.410433	10.839028
ic3285	12.409303	24.859667
ic3286	12.409578	23.747889
ic3287	12.410267	24.594722
ic3288	12.410947	24.949861
ic3289	12.415958	-26.030722
ic3290	12.419156	-39.7755
ic3291	12.413447	12.0185
ic3292	12.413433	18.195111
ic3293	12.414864	17.432417
ic3294	12.413814	25.597472
ic3295	12.413606	28.707833
ic3296	12.416067	24.382861
ic3297	12.41615	26.771194
ic3298	12.417722	17.015333
ic3299	12.417539	27.374472
ic3300	12.41805	25.957556
ic3301,ic3307	12.421539	14.172556
ic3302	12.419564	25.879806
ic3303	12.420889	12.714611
ic3304	12.419922	25.424278
ic3305	12.420694	11.849611
ic3306	12.420133	27.402361
ic3308	12.421725	26.715111
ic3309	12.422258	28.381
ic3310	12.432028	15.680528
ic3311	12.425864	12.260333
ic3312	12.424972	23.581639
ic3313	12.426789	15.829833
ic3314	12.425414	23.591056
ic3315	12.427481	12.31375
ic3316	12.426708	26.16325
ic3317	12.427475	25.343917
ic3318	12.430514	9.762806
ic3319	12.430814	10.391
ic3320,ngc4390	12.430742	10.459056
ic3321	12.429494	26.082528
ic3322	12.431694	7.554778
ic3322a	12.428489	7.216667
ic3323	12.430022	27.542389
ic3324	12.430322	26.739889
ic3325	12.430964	23.895917
ic3326	12.431319	23.768444
ic3327	12.434106	14.880361
ic3328	12.432758	10.053778
ic3329	12.4322	27.564111
ic3330	12.432308	30.843583
ic3331	12.434811	11.812222
ic3332	12.434775	25.279833
ic3333	12.435769	13.132944
ic3334	12.435981	28.465833
ic3335	12.438647	26.129306
ic3336	12.438858	26.838444
ic3337	12.439297	25.311528
ic3338	12.439522	25.886222
ic3339,ngc4411	12.441694	8.872222
ic3340	12.442419	16.844667
ic3341	12.439775	27.745528
ic3342	12.440936	27.138639
ic3343	12.443083	8.874278
ic3344	12.442331	13.578778
ic3345	12.442594	24.368861
ic3346	12.445675	11.379722
ic3347	12.445714	10.918583
ic3348	12.443919	25.624889
ic3349	12.446406	12.453972
ic3350	12.446231	9.442611
ic3351	12.444719	27.605583
ic3352	12.446611	8.7575
ic3353	12.445856	27.912333
ic3354	12.447628	12.097139
ic3355	12.447539	13.175722
ic3356	12.447358	11.559028
ic3357	12.447597	9.7775
ic3358	12.448428	11.663972
ic3359	12.447611	23.498167
ic3360	12.447422	26.046639
ic3361	12.448486	10.665861
ic3362	12.448447	26.690083
ic3363	12.450853	12.560806
ic3364	12.451364	25.56325
ic3365	12.453106	15.896667
ic3366	12.453367	9.410194
ic3367	12.453306	26.95675
ic3368	12.455661	16.428583
ic3369	12.454706	16.024472
ic3370	12.460369	-39.337778
ic3371	12.456181	10.866778
ic3372	12.456817	25.287222
ic3373	12.457725	25.453917
ic3374	12.4593	10.003778
ic3375	12.461211	27.36475
ic3376	12.463983	26.993528
ic3377	12.464431	24.942167
ic3378	12.467086	17.296306
ic3379	12.46785	17.30575
ic3380	12.468203	26.672861
ic3381	12.4708	11.789833
ic3382	12.470428	13.570694
ic3383	12.470089	10.297667
ic3384	12.470072	25.091333
ic3385	12.470819	25.432611
ic3386	12.473244	13.19575
ic3387	12.471894	27.995722
ic3388	12.474461	12.823667
ic3389	12.4732	27.844944
ic3390	12.474603	24.809333
ic3391	12.47425	18.415028
ic3392	12.478683	14.9995
ic3393	12.478253	12.915917
ic3394	12.478114	26.798417
ic3395	12.479028	25.03475
ic3396	12.479161	25.050222
ic3397	12.4796	25.731917
ic3399	12.482217	25.696083
ic3400	12.484139	9.406167
ic3401	12.483011	26.460083
ic3402	12.483144	28.861944
ic3403	12.483739	24.632667
ic3404	12.486311	7.153944
ic3405	12.483225	37.730111
ic3406	12.484064	27.640528
ic3407	12.484406	27.778861
ic3408	12.487719	11.875889
ic3409	12.489231	14.789306
ic3410	12.485047	19.004778
ic3411	12.486775	24.584194
ic3412	12.489625	9.989028
ic3413	12.489586	11.433889
ic3414	12.491328	6.771806
ic3415	12.489336	26.766222
ic3416	12.493044	10.793083
ic3417	12.494228	7.861278
ic3418	12.495533	11.404694
ic3419	12.495717	15.02475
ic3420	12.495156	13.446417
ic3421	12.494053	26.230611
ic3422	12.498503	14.688361
ic3423	12.496256	13.658778
ic3424	12.495844	24.408667
ic3425	12.498997	10.615333
ic3426	12.500406	13.598167
ic3427,ngc4482	12.502869	10.779472
ic3428	12.502086	23.675028
ic3429	12.502206	23.545139
ic3430	12.504689	9.085111
ic3431	12.506717	11.614472
ic3432	12.507733	14.160194
ic3433	12.507836	17.309722
ic3434	12.507572	18.809722
ic3435	12.511078	15.129694
ic3436	12.508314	19.673028
ic3437	12.512753	11.343194
ic3438,ngc4492	12.516586	8.077861
ic3439	12.516519	25.561806
ic3440	12.5181	12.029861
ic3441	12.517894	28.852694
ic3442	12.522275	14.115194
ic3443	12.521036	12.331778
ic3444	12.520525	27.549639
ic3445	12.522064	12.738
ic3446	12.523039	11.492389
ic3447	12.521639	10.680167
ic3448	12.523108	17.206417
ic3449	12.523039	25.914
ic3450	12.523561	26.796139
ic3451	12.523353	28.855194
ic3452,ngc4497	12.525703	11.624722
ic3453	12.52715	14.859806
ic3454	12.527403	27.495722
ic3455	12.529042	25.786083
ic3456	12.528819	28.357167
ic3457	12.530928	12.657
ic3458	12.528889	28.147361
ic3459	12.5322	12.174028
ic3460	12.530664	27.386889
ic3461	12.534094	11.890083
ic3462	12.535994	15.300944
ic3463	12.534606	12.319417
ic3464	12.533389	26.004833
ic3465	12.536733	12.061556
ic3466	12.534911	11.817917
ic3467	12.540158	11.787583
ic3468	12.537281	10.251472
ic3469	12.536383	25.802778
ic3470	12.539831	11.262972
ic3471	12.539672	16.018833
ic3472	12.53855	24.72825
ic3473	12.538644	18.244139
ic3474	12.543475	2.661528
ic3475	12.544739	12.771
ic3476	12.544967	14.050444
ic3477	12.543947	26.038444
ic3478	12.545611	14.196194
ic3479	12.544703	25.406111
ic3480	12.544858	26.828556
ic3481	12.54785	11.404389
ic3482	12.550278	27.830306
ic3483	12.552794	11.347333
ic3484	12.551472	17.403
ic3485	12.553128	9.217278
ic3486	12.553892	12.857833
ic3487	12.553733	9.397361
ic3488	12.552347	26.349361
ic3489	12.553806	12.247
ic3490	12.553861	10.928528
ic3491	12.552497	27.094389
ic3492	12.555494	12.853444
ic3493	12.555244	9.393194
ic3494	12.553808	27.584111
ic3495	12.554525	26.808806
ic3496	12.555364	26.755444
ic3497	12.557928	25.48875
ic3498	12.558047	26.738056
ic3499	12.5625	10.995722
ic3500	12.563797	13.962778
ic3501	12.564339	13.322444
ic3502	12.561758	26.617361
ic3503	12.563408	37.789306
ic3504	12.568847	6.886361
ic3505	12.569531	15.968222
ic3506	12.568539	12.741611
ic3507	12.567903	25.362833
ic3508	12.568597	26.670778
ic3509	12.569869	12.048972
ic3510	12.570781	11.071528
ic3511	12.569303	27.348639
ic3512	12.56935	27.361111
ic3513	12.569892	27.330556
ic3514	12.571053	26.700611
ic3515	12.571139	27.86225
ic3516	12.571428	27.452306
ic3517	12.575211	9.15475
ic3518	12.575358	9.623444
ic3519	12.577333	15.602694
ic3520	12.575503	13.503667
ic3521	12.577642	7.160194
ic3522	12.579328	15.220778
ic3523	12.577611	14.016778
ic3524	12.578639	14.244333
ic3525	12.579567	10.176694
ic3526	12.577947	25.684139
ic3527	12.578414	26.155111
ic3528	12.582194	15.565611
ic3529	12.580489	25.698778
ic3530	12.580367	17.814278
ic3531	12.582372	26.626583
ic3532	12.582644	25.880639
ic3533	12.583689	25.779722
ic3534	12.581147	14.978167
ic3535	12.586361	25.731972
ic3536	12.586803	26.533417
ic3537	12.589572	7.653
ic3538	12.587656	26.235528
ic3539	12.588914	23.983139
ic3540	12.590897	12.75025
ic3541	12.589367	23.97525
ic3542	12.594775	11.667167
ic3543,ngc4565c	12.594839	26.285833
ic3544	12.5965	14.300556
ic3545,ngc4555	12.594772	26.523111
ic3546,ngc4565b	12.594914	26.222194
ic3547	12.596914	26.329111
ic3548	12.599064	10.936306
ic3549	12.597458	26.395222
ic3550,ngc4559c	12.597811	27.932083
ic3551	12.598253	27.964167
ic3552	12.598306	27.993889
ic3553	12.598869	26.193056
ic3554	12.598664	27.927333
ic3555	12.598875	27.988889
ic3556	12.599572	26.966056
ic3557	12.602269	16.640861
ic3558	12.600778	11.849806
ic3559	12.600933	26.987361
ic3560	12.601086	27.078194
ic3561	12.601331	26.899611
ic3562	12.602933	9.922611
ic3563	12.602006	27.927361
ic3564	12.602247	27.928389
ic3565	12.603406	26.756111
ic3566	12.606033	11.164889
ic3567	12.606311	13.602861
ic3568	12.551883	82.563917
ic3569,ngc4561	12.602278	19.322917
ic3570	12.605078	24.078472
ic3571	12.605553	26.083778
ic3572	12.607758	11.6185
ic3573	12.607561	11.759111
ic3574	12.607731	12.405167
ic3575	12.608994	13.748417
ic3576	12.610467	6.620889
ic3577	12.610075	11.897139
ic3578	12.610947	11.101861
ic3579	12.609094	26.104139
ic3580	12.608119	18.3005
ic3581	12.610586	24.429028
ic3582	12.610253	26.234667
ic3583	12.612081	13.259333
ic3584	12.612528	12.233056
ic3585	12.611083	26.829944
ic3586	12.615236	12.520083
ic3587	12.613425	27.548528
ic3588,ngc4571	12.615661	14.217361
ic3589	12.617	6.937
ic3590	12.614086	27.278139
ic3591	12.617511	6.926639
ic3592,ngc4559a	12.614844	27.862028
ic3593,ngc4559b	12.614981	27.749111
ic3594	12.615664	26.1155
ic3595	12.618444	23.786889
ic3596	12.621917	26.520917
ic3597	12.623511	23.864056
ic3598	12.622522	28.208167
ic3599	12.628111	26.707667
ic3600	12.6281	27.129556
ic3601	12.631567	15.224667
ic3602	12.638417	10.072833
ic3603	12.637819	15.569806
ic3604	12.639089	11.730722
ic3605	12.639153	19.541333
ic3606	12.640303	12.610611
ic3607	12.642269	10.376528
ic3608	12.643703	10.475889
ic3609	12.642978	14.352417
ic3610	12.646428	26.872861
ic3611	12.65115	13.363528
ic3612,ic3616	12.651306	14.731139
ic3613	12.651331	13.759
ic3614	12.6503	26.302833
ic3615	12.650447	18.200667
ic3617	12.656944	7.965833
ic3618	12.654758	26.677778
ic3619	12.655217	24.142417
ic3620	12.655006	27.908639
ic3621	12.659328	15.502611
ic3622	12.659022	15.432056
ic3623	12.657672	27.102333
ic3624	12.659578	11.982194
ic3625	12.659214	10.967667
ic3626	12.658789	25.677389
ic3627	12.658889	27.497278
ic3628	12.660781	26.238889
ic3629	12.662961	13.533306
ic3630	12.662944	25.432528
ic3631	12.663336	12.973972
ic3632	12.666667	26.682222
ic3633	12.669792	9.896139
ic3634	12.669822	9.847778
ic3635	12.670383	12.874778
ic3636	12.670983	22.074556
ic3637	12.672103	14.715
ic3638	12.671278	10.518528
ic3639	12.681347	-36.755861
ic3640	12.673667	26.524167
ic3641	12.674133	26.521583
ic3642	12.673814	26.731222
ic3643	12.678019	12.406583
ic3644	12.676731	26.504611
ic3645	12.677114	26.541361
ic3646	12.677361	26.526194
ic3647	12.681419	10.475361
ic3648	12.681164	12.985
ic3649	12.680469	21.10475
ic3650	12.680142	26.472722
ic3651	12.681364	26.728139
ic3652	12.682933	11.1845
ic3653	12.687703	11.38725
ic3654	12.686806	22.589444
ic3655	12.68735	20.666194
ic3656	12.687203	22.594972
ic3657	12.688617	21.6725
ic3658	12.689064	14.700556
ic3659	12.691006	22.930806
ic3660	12.693567	21.093361
ic3661	12.693258	22.494861
ic3662	12.693408	23.425167
ic3663	12.694281	12.247389
ic3664	12.694875	19.944139
ic3665	12.696306	11.48825
ic3666	12.698158	7.845028
ic3667,ngc4618	12.692458	41.150778
ic3668	12.692469	41.124167
ic3669	12.693308	41.136583
ic3670	12.698617	11.774167
ic3671	12.697606	23.510667
ic3673	12.7012	21.138333
ic3674	12.701422	22.510778
ic3675,ngc4625	12.697978	41.273972
ic3676	12.703411	13.559833
ic3677	12.703289	20.884861
ic3678	12.703494	20.880472
ic3679	12.703119	22.818278
ic3680	12.700253	39.10425
ic3681	12.700486	39.083417
ic3682	12.705411	20.864444
ic3683	12.705733	20.871306
ic3684	12.707364	11.740306
ic3685	12.708956	6.870917
ic3686	12.71	10.565306
ic3687	12.704194	38.503333
ic3688,ngc4633	12.710383	14.357194
ic3689	12.710267	20.8505
ic3690	12.713664	10.357472
ic3691	12.713758	22.772222
ic3692	12.715	20.98975
ic3693	12.716117	10.681806
ic3694	12.718689	11.212
ic3695	12.718556	22.741944
ic3696	12.719344	19.928028
ic3697	12.716347	39.845667
ic3698	12.721472	11.211528
ic3699	12.721425	19.000194
ic3700	12.722222	19.265944
ic3701	12.725253	11.047139
ic3702	12.724547	10.873861
ic3703	12.722778	37.974528
ic3704	12.729336	10.770083
ic3705	12.728197	19.325278
ic3706	12.729997	9.231139
ic3707	12.724633	37.982694
ic3708	12.731264	13.137528
ic3709	12.734453	9.063333
ic3710	12.735958	12.116528
ic3711	12.735936	11.176611
ic3712	12.737958	10.374556
ic3713	12.734214	41.168917
ic3714	12.739744	10.188833
ic3715	12.739281	20.024333
ic3716	12.745872	8.102167
ic3717	12.739711	39.522306
ic3718	12.746106	12.351444
ic3719	12.746528	8.106917
ic3720	12.746522	12.064306
ic3721,ic3725	12.748089	18.75525
ic3722	12.747414	11.778583
ic3723	12.741819	40.736889
ic3724	12.748267	10.282361
ic3726	12.745164	40.679
ic3727	12.751572	10.900889
ic3728	12.750869	20.974083
ic3729	12.748089	39.351194
ic3730	12.751822	21.169583
ic3731	12.751461	12.446361
ic3732	12.753322	10.324444
ic3733	12.754644	6.956889
ic3734	12.752578	23.039056
ic3735	12.755672	13.692667
ic3736	12.755267	21.53575
ic3737	12.755519	21.958167
ic3738	12.75715	19.230861
ic3739	12.758964	12.997361
ic3740	12.758506	20.815944
ic3741	12.759244	19.204139
ic3742	12.758894	13.332583
ic3743	12.761472	11.102111
ic3744	12.761522	19.500333
ic3745	12.762461	19.17725
ic3746	12.758864	37.823556
ic3747	12.759561	37.968528
ic3748	12.764144	19.430333
ic3749	12.764272	19.535583
ic3750	12.76585	19.103861
ic3751	12.762528	37.823056
ic3752	12.767803	19.011444
ic3753	12.767883	19.121167
ic3754	12.770983	8.348444
ic3755	12.769281	19.15725
ic3756	12.769472	11.914611
ic3757	12.766606	38.515306
ic3758	12.766575	40.774861
ic3759	12.771603	20.783
ic3760	12.771739	11.873583
ic3761	12.774258	20.289139
ic3762	12.777111	22.246361
ic3763	12.779453	21.985111
ic3765	12.776431	38.573889
ic3766	12.781533	19.110583
ic3767	12.782078	10.182417
ic3768	12.777975	40.597667
ic3769	12.780019	40.470194
ic3770	12.787694	9.199111
ic3771	12.781303	39.173056
ic3772	12.782247	36.530944
ic3773	12.787583	10.203583
ic3774	12.783636	36.288306
ic3775	12.787806	11.760222
ic3776	12.786725	22.484611
ic3777	12.790375	9.143472
ic3778	12.783881	40.596417
ic3779	12.789067	12.166417
ic3780	12.785578	40.236028
ic3781	12.790158	22.569778
ic3782	12.787686	40.36775
ic3783	12.791067	40.566583
ic3784	12.797417	19.384056
ic3785	12.797825	19.275222
ic3786	12.793583	39.046028
ic3787	12.794958	40.623778
ic3788	12.802017	18.868861
ic3789	12.801972	20.194028
ic3790	12.804069	11.107583
ic3791,ngc4695	12.792253	54.374833
ic3792	12.803933	11.086333
ic3793	12.803303	19.151694
ic3794	12.805975	19.170306
ic3795	12.801419	40.719639
ic3796	12.8075	20.037694
ic3797	12.809697	11.597806
ic3798	12.811922	9.241028
ic3799	12.816567	-14.399222
ic3800	12.807342	36.575861
ic3801	12.816847	10.955972
ic3802	12.811836	38.246444
ic3803	12.817889	10.631806
ic3804,ngc4711	12.812742	35.332694
ic3805	12.811842	38.253056
ic3806	12.815378	14.907889
ic3807	12.824944	-4.402278
ic3808	12.816322	40.595917
ic3809	12.817919	36.489083
ic3810	12.81755	40.646639
ic3811	12.823769	21.462139
ic3812	12.831611	-6.717444
ic3813	12.833978	-25.920694
ic3814	12.825669	20.050472
ic3815	12.827369	19.275028
ic3816	12.824575	37.230278
ic3817	12.828742	22.831361
ic3818	12.829647	21.752222
ic3819	12.837881	-14.38075
ic3820	12.827486	37.117167
ic3821	12.832653	20.969028
ic3822	12.839647	-14.321861
ic3823	12.828883	40.883444
ic3824	12.841819	-14.425917
ic3825	12.843625	-14.482806
ic3826	12.844417	-9.031083
ic3827,ic3838	12.847811	-14.491889
ic3828	12.839083	37.948944
ic3829	12.870361	-29.840667
ic3830	12.847603	19.836694
ic3831	12.855164	-14.573583
ic3832	12.847	39.810472
ic3833,ngc4722	12.858997	-13.330028
ic3834	12.859	-14.221389
ic3835	12.848844	40.18675
ic3836	12.851033	40.184222
ic3837	12.859169	19.723056
ic3839	12.86285	20.420972
ic3840	12.862806	21.735194
ic3841	12.864028	22.3445
ic3842	12.859967	40.371361
ic3843	12.860886	39.001306
ic3844	12.868472	39.81825
ic3845	12.869072	38.619
ic3846	12.877561	13.647222
ic3847	12.876039	22.064722
ic3848	12.877831	21.416111
ic3849	12.876897	40.772222
ic3850	12.877644	40.103056
ic3851	12.884647	21.909167
ic3852	12.88425	35.773444
ic3853	12.886194	38.829278
ic3854	12.887372	40.848167
ic3855	12.889636	36.786
ic3856	12.896089	20.092083
ic3857	12.898906	19.607139
ic3858	12.898761	20.789028
ic3859	12.905517	-9.117722
ic3860	12.901864	19.300722
ic3861	12.897453	38.281806
ic3862	12.898044	36.086944
ic3863	12.898289	38.480444
ic3864	12.903428	18.951278
ic3865	12.903931	18.868944
ic3866	12.904228	22.361833
ic3867	12.905439	18.941806
ic3868	12.905833	18.990333
ic3869	12.905908	18.971417
ic3870	12.905994	22.381694
ic3871	12.907131	18.929139
ic3872	12.908489	18.963167
ic3873	12.908778	18.882667
ic3874	12.909561	18.957
ic3875	12.910325	22.036444
ic3876	12.913425	19.015333
ic3877	12.913522	19.178278
ic3878	12.908211	40.069722
ic3879	12.908853	38.628556
ic3880	12.913331	22.502222
ic3881	12.914986	19.118056
ic3882	12.914919	22.575583
ic3883	12.920422	-8.11975
ic3884	12.916036	19.681278
ic3885	12.911869	37.154722
ic3886	12.91675	19.011694
ic3887	12.912158	40.304639
ic3888	12.912881	39.571278
ic3889	12.914139	36.016833
ic3890	12.913961	37.185306
ic3891	12.916181	36.052722
ic3892	12.918344	39.221944
ic3893	12.918736	38.623861
ic3894	12.924336	19.069111
ic3895	12.919231	39.20325
ic3896	12.945342	-50.346861
ic3897	12.921972	39.672611
ic3898	12.923289	37.582889
ic3899	12.927961	20.636444
ic3900	12.928139	27.25075
ic3901	12.930694	21.939028
ic3902	12.927383	35.995833
ic3903	12.927428	40.399667
ic3904	12.929333	36.293417
ic3905	12.935719	19.852083
ic3906	12.93085	40.463861
ic3907	12.938383	18.784028
ic3908	12.944617	-7.562778
ic3909	12.934117	40.385444
ic3910	12.934592	39.719889
ic3911	12.935953	35.63825
ic3912	12.935428	39.910667
ic3913	12.941269	27.291278
ic3914	12.939661	36.360917
ic3915	12.944172	20.291694
ic3916	12.941992	38.613444
ic3917	12.947675	22.006056
ic3918	12.948206	22.373611
ic3919	12.946864	38.58875
ic3920	12.947236	39.958667
ic3921	12.949069	38.6395
ic3922	12.949306	38.478278
ic3923	12.950314	37.955722
ic3924	12.956911	18.781528
ic3925	12.9542	36.422
ic3926	12.958447	22.811944
ic3927	12.969553	-22.876028
ic3928	12.955081	40.441611
ic3929	12.961414	20.396889
ic3930	12.956219	38.764917
ic3931	12.965889	19.617639
ic3932	12.968139	19.583444
ic3933	12.965889	36.645056
ic3934	12.971544	18.825417
ic3935,ngc4849	12.970189	26.396889
ic3936	12.972203	19.058278
ic3937	12.973539	18.818667
ic3938	12.973711	18.752639
ic3939	12.97445	18.751861
ic3940	12.971242	35.838944
ic3941	12.970531	39.772833
ic3942	12.972192	36.10875
ic3943	12.976764	28.11375
ic3944	12.979097	23.781056
ic3945	12.974897	39.935917
ic3946	12.9802	27.810389
ic3947	12.981139	27.785056
ic3948	12.982819	24.061361
ic3949	12.982225	27.833361
ic3950	12.985033	18.735611
ic3951	12.986167	18.764278
ic3952	12.981153	38.8695
ic3953	12.985867	23.086611
ic3954	12.986847	19.272944
ic3955	12.985008	27.996694
ic3956	12.982328	37.398167
ic3957	12.985414	27.767778
ic3958	12.986503	24.022278
ic3959	12.985611	27.784139
ic3960	12.985544	27.855
ic3961,ngc4861	12.983983	34.859444
ic3962	12.987494	23.668
ic3963	12.987083	27.774611
ic3964	12.987147	27.850944
ic3965	12.989633	18.842944
ic3966	12.986978	35.855333
ic3967	12.986917	36.129278
ic3968	12.990414	27.973194
ic3969	12.992475	19.652
ic3970	12.986508	40.401917
ic3971	12.992164	22.844806
ic3972	12.988097	37.279139
ic3973	12.991894	27.884222
ic3974,ngc4947	13.088944	-35.337417
ic3975	12.987692	38.88275
ic3976	12.9915	27.850139
ic3977	12.988794	36.798083
ic3978	12.993736	19.622222
ic3979	12.989097	36.324333
ic3980	12.9885	39.15125
ic3981	12.989292	37.227806
ic3982	12.988497	40.080528
ic3983	12.989031	39.246639
ic3984	12.994517	19.623083
ic3985	12.995319	19.591111
ic3986	13.025594	-32.291056
ic3987	12.990289	38.733444
ic3988	12.990783	37.244972
ic3989	12.991317	36.756583
ic3990	12.994197	28.895528
ic3991	12.994386	28.926583
ic3992	12.992581	36.771833
ic3993	12.991797	40.601778
ic3994	12.997456	22.71675
ic3995	12.992758	39.039778
ic3996	12.992083	40.467556
ic3997	12.993592	36.695667
ic3998	12.996328	27.973861
ic3999,ngc4862	12.991894	-14.132333
ic4000	12.993506	39.58775
ic4001	12.993869	38.87025
ic4002	12.994614	36.763472
ic4003	12.994258	38.815583
ic4004	12.995214	38.811306
ic4005	13.000706	22.639917
ic4006	12.996867	37.011083
ic4007	13.001942	19.964667
ic4008	13.001594	22.3505
ic4009	12.998	36.66075
ic4010	12.998344	37.859111
ic4011	13.001775	28.004139
ic4012	13.002219	28.078556
ic4013	12.999397	37.199389
ic4014	13.003861	22.499611
ic4015,ngc4893	12.999892	37.193389
ic4016,ngc4893a	12.999956	37.188139
ic4017	13.004422	22.555694
ic4018	12.999289	40.488722
ic4019	13.004842	23.720833
ic4020	13.000944	38.609889
ic4021	13.004094	28.041306
ic4022	13.001369	38.478917
ic4023	13.007372	19.097333
ic4024	13.001103	40.509139
ic4025	13.007878	19.105028
ic4026	13.00615	28.047
ic4027	13.003783	37.141417
ic4028	13.004481	36.254111
ic4029	13.003944	38.759722
ic4030	13.007769	27.955972
ic4031	13.0043	39.144944
ic4032	13.007125	28.867806
ic4033	13.007886	27.972417
ic4034	13.005442	37.046194
ic4035	13.004817	40.301444
ic4036	13.005764	36.909056
ic4037	13.005394	39.002639
ic4038	13.006047	37.039361
ic4039	13.010939	21.691722
ic4040	13.010536	28.057361
ic4041	13.011347	27.996611
ic4042	13.011881	27.971389
ic4043	13.009633	37.071917
ic4044	13.013169	27.922167
ic4045	13.013511	28.090778
ic4046	13.010953	36.685917
ic4047	13.016025	19.687
ic4048	13.010597	39.830972
ic4049	13.01185	36.345556
ic4050	13.012172	36.739861
ic4051	13.014322	28.042806
ic4052	13.011644	39.667639
ic4053	13.017031	22.924722
ic4054	13.017044	22.905028
ic4055	13.017397	22.908556
ic4056	13.012303	39.754139
ic4057	13.018128	23.157694
ic4058	13.019261	19.494167
ic4059	13.020964	19.273556
ic4060	13.0146	40.584556
ic4061	13.016011	39.58275
ic4062	13.016289	39.858944
ic4063	13.018514	39.245194
ic4064	13.018536	39.841472
ic4065	13.019719	39.744472
ic4066	13.027822	19.272611
ic4067	13.02225	39.940361
ic4068	13.022272	39.899056
ic4069	13.02355	36.112722
ic4070	13.028692	19.301944
ic4071	13.034469	-7.603194
ic4072	13.023844	37.353722
ic4073	13.023808	39.914278
ic4074	13.030272	19.008861
ic4075	13.030156	19.965
ic4076	13.030164	23.389111
ic4077	13.026125	37.386222
ic4078	13.026572	36.593222
ic4079	13.032442	19.248806
ic4080	13.032722	19.254694
ic4081	13.032028	22.771028
ic4082	13.027525	37.341639
ic4083	13.027475	38.142361
ic4084	13.028064	36.965667
ic4085	13.027275	39.702694
ic4086	13.028567	36.648417
ic4087	13.033447	19.995194
ic4089	13.033847	19.502889
ic4090	13.029528	36.837944
ic4091	13.036933	19.893
ic4092	13.037119	19.184167
ic4093	13.034442	28.99475
ic4094	13.032942	37.795028
ic4095	13.038994	19.099694
ic4096	13.038044	24.010833
ic4097	13.034706	36.605444
ic4098	13.0344	37.980889
ic4099	13.039786	24.029167
ic4100	13.034697	40.408361
ic4101	13.037153	39.940361
ic4102	13.038331	36.152444
ic4103	13.038625	38.0175
ic4104	13.038367	38.592417
ic4105	13.038611	38.271278
ic4106	13.044011	28.114583
ic4107	13.044964	21.997389
ic4108	13.042092	38.4785
ic4109	13.049436	19.003694
ic4110	13.049525	19.226972
ic4111	13.049047	28.070417
ic4112	13.045878	37.212167
ic4113	13.050919	20.473389
ic4114	13.044953	40.104528
ic4115	13.046869	37.223222
ic4116	13.052811	19.083361
ic4117	13.046833	40.524889
ic4118	13.047694	38.292944
ic4119	13.054214	19.232778
ic4120	13.050431	37.081667
ic4121	13.055978	19.282306
ic4122	13.056786	20.196917
ic4123	13.051617	38.314472
ic4124	13.058769	22.846806
ic4125	13.059714	18.803389
ic4126	13.060125	19.323444
ic4127	13.054833	38.046917
ic4128	13.061456	20.216639
ic4129	13.062214	18.877139
ic4130	13.062942	19.271528
ic4131	13.057106	38.951278
ic4132	13.0594	38.377583
ic4133	13.064111	27.988389
ic4134,ngc4920	13.034486	-11.378417
ic4135	13.060386	40.248972
ic4136,ngc4942	13.071975	-7.649444
ic4137	13.066472	22.739972
ic4138	13.067253	20.6655
ic4139	13.067819	19.294972
ic4140	13.068344	20.096361
ic4141	13.068814	19.210639
ic4142	13.063108	38.195083
ic4143	13.062639	40.207083
ic4144	13.063908	36.943389
ic4145	13.063825	38.286583
ic4146	13.06955	19.27825
ic4147	13.069286	20.250889
ic4148	13.069636	19.259167
ic4149	13.069672	22.289667
ic4150	13.070289	21.986722
ic4151	13.066372	36.857889
ic4152	13.066239	38.198611
ic4153	13.074047	19.044972
ic4154	13.074519	23.575028
ic4155	13.069139	40.015444
ic4156,ngc4948	13.082211	-7.947694
ic4157	13.071828	38.663583
ic4158	13.073511	36.479889
ic4159	13.079442	22.242139
ic4160	13.080017	22.892472
ic4161	13.076478	39.977472
ic4162	13.084164	20.554806
ic4163	13.085558	20.770722
ic4164	13.087358	20.547111
ic4165	13.082489	39.924917
ic4166	13.088497	31.442306
ic4167	13.091875	21.910028
ic4168	13.086308	40.049694
ic4169	13.086692	38.772472
ic4170	13.093014	21.135028
ic4171	13.088558	36.102889
ic4172	13.109267	22.850389
ic4173,ngc4933a	13.065203	-11.505056
ic4174	13.091267	36.396417
ic4175	13.096519	20.374694
ic4176,ngc4933b	13.065761	-11.498056
ic4177	13.108042	-13.571639
ic4178	13.094861	36.017472
ic4179	13.096083	37.197806
ic4180	13.115692	-23.917111
ic4181	13.101783	21.493889
ic4182	13.097094	37.604889
ic4183	13.103211	21.504361
ic4184	13.097714	38.837389
ic4185	13.103511	21.773028
ic4186	13.099267	36.986056
ic4187	13.099894	36.298472
ic4188	13.100647	36.328222
ic4189	13.100986	35.980333
ic4190	13.101772	37.610028
ic4191	13.146453	-67.64375
ic4192	13.102389	37.605556
ic4193	13.101758	39.423611
ic4194	13.102164	38.873583
ic4195	13.104286	37.039778
ic4196,ngc4970	13.126039	-24.008556
ic4197	13.134536	-23.796861
ic4198,ngc4979	13.128561	24.810583
ic4199	13.125742	35.859833
ic4200	13.159656	-51.968583
ic4201	13.130894	35.834861
ic4202	13.142106	24.700778
ic4203	13.138631	40.427889
ic4204	13.139328	39.461167
ic4206	13.156094	39.02225
ic4207	13.157425	37.822944
ic4208	13.160553	37.255583
ic4209	13.172914	-7.170694
ic4210,ngc5004b	13.179903	29.709889
ic4211	13.182356	37.17625
ic4212	13.200831	-6.9925
ic4213	13.203117	35.669694
ic4214	13.295192	-32.101694
ic4215	13.271342	25.405222
ic4216	13.283853	-10.77
ic4217	13.287022	-13.154083
ic4218	13.284281	-2.261278
ic4219	13.308261	-31.630889
ic4220	13.298422	-13.605472
ic4221	13.308431	-14.608889
ic4223	13.315336	7.7955
ic4224	13.318069	-2.515306
ic4225	13.333597	31.981389
ic4226	13.341781	32.003917
ic4227	13.348189	32.190778
ic4228	13.359472	25.51625
ic4229	13.373925	-2.418278
ic4230	13.366444	26.733861
ic4231	13.38705	-26.300389
ic4232	13.389569	-26.1095
ic4233,ngc5124	13.414008	-30.307528
ic4234	13.383297	27.116417
ic4235	13.398047	-12.743361
ic4236,ngc5118	13.390958	6.392556
ic4237	13.4091	-21.136833
ic4238	13.399986	30.932417
ic4239	13.407064	30.959278
ic4240	13.407656	30.977917
ic4241	13.412931	26.738417
ic4242	13.411367	31.0265
ic4243	13.4309	-27.626889
ic4244	13.415631	26.463528
ic4245	13.433069	-26.677722
ic4246	13.433403	-26.678056
ic4247	13.445675	-30.362417
ic4248	13.44645	-29.881361
ic4249	13.451822	-27.956389
ic4250	13.435817	26.477167
ic4251	13.456744	-29.444361
ic4252	13.457778	-27.324778
ic4253	13.458992	-27.872139
ic4254	13.462603	-27.222528
ic4255	13.4667	-27.354306
ic4256	13.450886	30.976833
ic4257	13.455647	46.867
ic4258	13.464794	28.508194
ic4259	13.491153	-30.134944
ic4260	13.494561	-28.266083
ic4261	13.496572	-28.006361
ic4262	13.506417	-28.270583
ic4263	13.475886	46.927194
ic4264	13.504922	-27.928444
ic4265	13.506381	-25.765556
ic4266	13.484897	37.61175
ic4267	13.510028	-26.256056
ic4268	13.486758	37.6605
ic4269	13.489178	37.623083
ic4270	13.513636	-25.333667
ic4271	13.489278	37.411667
ic4272	13.521267	-29.957361
ic4273	13.524961	-28.893444
ic4274,ngc5189	13.559142	-65.974056
ic4275	13.530917	-29.732389
ic4276	13.535072	-28.156833
ic4277	13.504644	47.314167
ic4278	13.507653	47.246889
ic4279	13.541936	-27.127472
ic4280	13.548167	-24.207139
ic4281	13.543958	-27.169639
ic4282	13.522158	47.183861
ic4283	13.5363	28.389111
ic4284	13.525539	46.795111
ic4285	13.529317	46.821611
ic4286	13.559903	-27.631222
ic4287	13.544167	25.441111
ic4288	13.575117	-27.304222
ic4289	13.579947	-27.127083
ic4290	13.588772	-28.021806
ic4291	13.615669	-62.093111
ic4292	13.596278	-27.673861
ic4293	13.600628	-25.882306
ic4294	13.608675	-28.781139
ic4295	13.609572	-29.089444
ic4296	13.610842	-33.965833
ic4297	13.588681	26.424778
ic4298	13.609647	-26.553861
ic4299	13.613189	-34.065806
ic4300	13.590333	33.419806
ic4301	13.593278	33.3745
ic4302	13.593319	33.479583
ic4303	13.621728	-28.657972
ic4304	13.599411	33.430028
ic4305	13.599547	33.473917
ic4306	13.605456	33.423444
ic4307	13.610047	27.242194
ic4308	13.614544	32.733361
ic4309	13.647233	-29.662722
ic4310	13.649206	-25.845722
ic4311	13.668878	-51.036139
ic4312	13.67525	-51.070889
ic4313	13.639086	26.759778
ic4314	13.640297	26.7425
ic4315	13.667553	-25.474556
ic4316	13.671781	-28.892222
ic4317	13.696061	27.106361
ic4318	13.722969	-28.967944
ic4319	13.724047	-29.803472
ic4320	13.734367	-27.231694
ic4321	13.742014	-30.139583
ic4322	13.728931	25.392139
ic4323	13.751911	-28.65125
ic4324	13.757586	-30.227222
ic4325	13.794347	-29.434361
ic4326	13.805969	-29.626389
ic4327	13.812167	-30.2175
ic4328	13.817472	-29.937028
ic4329	13.818142	-30.295861
ic4330	13.787458	-28.331806
ic4331	13.823503	25.154667
ic4332	13.831264	25.190889
ic4333	14.089053	-84.272694
ic4334	13.830075	29.694083
ic4335	13.829186	33.673639
ic4336	13.845381	39.706778
ic4337	13.872022	14.271917
ic4338,ngc5334	13.881794	-1.114639
ic4339	13.891342	37.539028
ic4340	13.892647	37.386972
ic4341	13.892847	37.52225
ic4342	13.906142	25.153083
ic4343	13.9155	25.122639
ic4344	13.920164	25.021444
ic4345	13.920386	25.051806
ic4346	13.927936	25.153056
ic4347,ngc5367	13.962186	-39.978417
ic4348	13.929192	25.203111
ic4349	13.929539	25.151917
ic4350	13.953867	-25.245806
ic4351	13.965072	-29.315722
ic4352	13.973644	-34.517333
ic4353	13.951028	37.729056
ic4354	13.97525	-12.605361
ic4355	13.968367	28.422694
ic4356	13.979194	37.490667
ic4357	14.012136	31.894167
ic4358	14.059494	-10.15125
ic4359	14.089814	-45.269778
ic4360	14.072594	-11.424833
ic4361	14.068742	-9.768889
ic4362	14.089506	-41.818972
ic4363	14.070083	-9.641639
ic4364	14.072144	-9.993278
ic4365,ngc5437	14.06315	9.523694
ic4366	14.086522	-33.760111
ic4367	14.093494	-39.203361
ic4368	14.079567	-9.96225
ic4369	14.068297	33.320722
ic4370	14.069406	33.346
ic4371	14.069686	33.307806
ic4372	14.096136	-10.900083
ic4373	14.095325	25.231361
ic4374	14.124933	-27.017861
ic4375,ngc5488	14.134197	-33.314917
ic4376	14.180686	-30.79275
ic4377	14.283003	-75.647194
ic4378	14.202658	-34.265333
ic4379	14.202844	-34.272722
ic4380	14.167256	37.549861
ic4381,ngc5008	14.182567	25.497222
ic4382	14.184039	25.519361
ic4383,ngc5504b	14.203533	15.868889
ic4384	14.198894	27.113917
ic4385	14.242144	-42.323611
ic4386	14.250658	-43.961333
ic4387	14.250486	-43.990111
ic4388	14.267633	-31.752639
ic4389	14.2795	-40.5525
ic4390	14.283111	-44.977333
ic4391	14.274178	-31.684972
ic4392	14.264769	-13.05125
ic4393	14.296931	-31.349083
ic4394	14.272878	39.697694
ic4395	14.289189	26.857444
ic4396	14.291733	28.8
ic4397	14.299644	26.412556
ic4398	14.300956	28.866389
ic4399	14.306656	26.385889
ic4400	14.370403	-60.569806
ic4401	14.323631	-4.489139
ic4402	14.353636	-46.297889
ic4403	14.304686	31.653833
ic4404	14.180603	78.628306
ic4405	14.321275	26.298583
ic4406	14.374022	-44.150194
ic4407	14.393572	-5.983222
ic4408	14.353636	29.9935
ic4409	14.35925	31.585528
ic4410	14.370542	17.397333
ic4411	14.416972	-35.020611
ic4412,ngc5594	14.386197	26.265806
ic4413	14.382589	37.527417
ic4415	14.407422	16.639611
ic4416	14.404839	29.635806
ic4417	14.414914	17.037917
ic4418	14.424233	25.526278
ic4419	14.431853	16.632528
ic4420	14.427614	25.378361
ic4421	14.475364	-37.58375
ic4422	14.433092	30.473722
ic4423	14.438261	26.246139
ic4425	14.445606	27.189528
ic4426	14.454747	16.830972
ic4427	14.449881	26.863972
ic4428	14.457097	16.190833
ic4429	14.460381	16.899861
ic4430	14.488722	-33.455111
ic4432	14.480489	-39.552194
ic4433	14.464819	16.195556
ic4434	14.465206	16.207167
ic4435	14.456744	37.471444
ic4436	14.466161	26.5045
ic4437	14.458794	41.503222
ic4438	14.476242	17.334556
ic4439	14.477789	17.02475
ic4440	14.483122	17.320583
ic4441,ic4444	14.527394	-43.418444
ic4442	14.479242	28.96425
ic4443	14.488192	16.181556
ic4445	14.531836	-46.035306
ic4446	14.4837	37.463139
ic4447	14.488328	30.832222
ic4448	14.674433	-78.809222
ic4449	14.522664	15.240861
ic4450	14.536761	28.556833
ic4451	14.576983	-36.285833
ic4452	14.540953	27.427417
ic4453	14.574625	-27.518556
ic4454	14.554636	17.711806
ic4455,ngc5664	14.562117	-14.619694
ic4456	14.569214	16.184028
ic4457	14.574689	18.224694
ic4458	14.634964	-39.505972
ic4459	14.575611	30.974667
ic4460	14.576814	30.279389
ic4461	14.583439	26.531917
ic4462	14.583861	26.543917
ic4463	14.596944	16.019278
ic4464	14.630278	-36.878
ic4465	14.597544	15.572917
ic4466	14.613364	18.343778
ic4467	14.614908	18.370639
ic4468	14.640761	-22.367611
ic4469	14.622358	18.249333
ic4470	14.473025	78.885611
ic4471,ngc5697	14.608906	41.685889
ic4472	14.669678	-44.314583
ic4473	14.631706	15.861667
ic4474	14.639528	23.42875
ic4475	14.639794	23.333556
ic4476	14.664403	-16.24475
ic4477	14.643122	28.459389
ic4478	14.653525	15.877389
ic4479	14.646083	28.505444
ic4480	14.662675	18.492361
ic4481	14.669475	16.141444
ic4482	14.670128	18.943278
ic4483	14.672086	16.685222
ic4484	14.795522	-73.305944
ic4485	14.675406	28.668861
ic4486	14.694664	18.557222
ic4487	14.697831	18.577
ic4488	14.714606	18.620278
ic4489	14.721097	18.528611
ic4490	14.755908	-36.173361
ic4492	14.709408	37.452333
ic4493,ngc5747	14.739111	12.129722
ic4494	14.740428	15.551389
ic4495	14.737381	23.558389
ic4496	14.731828	33.406556
ic4497	14.739128	28.551028
ic4498	14.750219	26.301139
ic4499	15.005347	-82.2135
ic4500	14.743239	37.482472
ic4501	14.790408	-22.406028
ic4502	14.754397	37.300361
ic4503	14.777642	16.146444
ic4504	14.776939	31.699194
ic4505	14.775936	33.408611
ic4506	14.777761	33.401222
ic4507	14.795044	18.455722
ic4508	14.797614	31.768278
ic4509	14.807517	31.791583
ic4510	14.844642	-20.730889
ic4511	14.868133	-40.494917
ic4512	14.83175	27.700806
ic4513	14.871342	-20.727917
ic4514	14.848733	27.578528
ic4515	14.851853	37.494806
ic4516	14.906514	16.355278
ic4517	14.909747	23.643278
ic4518	14.961917	-43.131667
ic4518a	14.961439	-43.132111
ic4518b	14.96235	-43.131361
ic4519	14.912372	37.412722
ic4520	14.918614	33.724444
ic4521	14.990958	25.584083
ic4522	15.191367	-75.859972
ic4523	15.086261	-43.509528
ic4524	15.0351	25.6015
ic4525	15.040239	25.6385
ic4526	15.043944	23.350444
ic4527	15.094728	-42.449528
ic4528	15.025936	49.112472
ic4529	15.107217	-43.232639
ic4530	15.062586	26.100861
ic4531	15.074011	23.414944
ic4532	15.081614	23.256611
ic4533	15.075094	27.792861
ic4534	15.111603	23.641917
ic4535	15.144889	37.570333
ic4536	15.221453	-18.137278
ic4537	15.292344	2.047389
ic4538	15.353225	-23.658417
ic4539	15.308653	32.392861
ic4540	15.334197	1.786583
ic4541	15.498769	-70.584944
ic4542	15.368164	33.148583
ic4544	15.489719	-50.583444
ic4545	15.69105	-81.625944
ic4546	15.449558	28.852611
ic4547	15.454186	28.788972
ic4548	15.456672	28.849833
ic4549	15.487381	32.825556
ic4550,ngc5946	15.591269	-50.659722
ic4551,ngc5964	15.626728	5.974028
ic4552	15.648581	4.583056
ic4554	15.584675	23.479278
ic4555	15.804114	-78.178861
ic4556	15.589569	25.297139
ic4557	15.576925	39.728889
ic4558	15.596167	25.345889
ic4559	15.5982	25.341139
ic4560	15.598356	39.814111
ic4561	15.613075	25.416806
ic4562	15.599167	43.49325
ic4563	15.601022	39.831528
ic4564	15.607517	43.518778
ic4565	15.609758	43.424889
ic4566	15.611711	43.539333
ic4567	15.620353	43.298306
ic4568	15.668806	28.152278
ic4569	15.680106	28.292083
ic4570	15.689608	28.22975
ic4571	15.814306	-67.323472
ic4572	15.698386	28.134
ic4573	15.703428	23.799972
ic4574	15.699789	28.240333
ic4575	15.705458	23.807639
ic4576	15.709861	23.670056
ic4577	15.712656	23.792639
ic4578	15.886294	-74.825278
ic4579	15.714308	23.773167
ic4580	15.720622	28.356833
ic4581	15.733756	28.277028
ic4582	15.760958	28.088667
ic4583	15.772761	23.809028
ic4584	16.003406	-66.383278
ic4585	16.0049	-66.322278
ic4586,ngc6014	15.932611	5.931889
ic4587	15.997669	25.940639
ic4588	16.084514	23.917139
ic4589	16.123497	-6.385306
ic4590	16.139208	28.478694
ic4591,lbn1096	16.205044	-27.92775
ic4592,lbn1113	16.199631	-19.454667
ic4593	16.195694	12.071389
ic4594,ngc6075	16.189608	23.965
ic4595	16.345678	-70.142611
ic4596	16.267669	-22.625389
ic4597	16.294369	-34.365944
ic4598	16.303697	-31.442889
ic4599	16.323103	-42.260139
ic4600	16.302408	-22.785528
ic4601	16.338278	-20.087306
ic4602,ngc6132	16.394122	11.78625
ic4603,lbn1109	16.423467	-24.468361
ic4604,lbn1111,rhoophnebula	16.425325	-23.436583
ic4605,lbn1110	16.503467	-25.115167
ic4606	16.526081	-26.056528
ic4607	16.504408	24.574361
ic4608	16.781661	-77.488694
ic4609	16.55045	22.797389
ic4610	16.560878	39.257639
ic4611	16.561761	39.185139
ic4612	16.563783	39.263194
ic4613	16.619486	36.130583
ic4614	16.629772	36.115
ic4615,ngc6196	16.631644	36.073056
ic4616,ngc6197	16.6333	35.9955
ic4617	16.702239	36.684083
ic4618	16.963892	-76.992972
ic4619	16.736422	17.759167
ic4620	16.808344	19.305389
ic4621	16.847547	8.783667
ic4622	16.868975	-16.23625
ic4623	16.851483	22.527417
ic4624	16.859317	17.449111
ic4625,ngc6240	16.883019	2.400917
ic4626	16.889286	2.338722
ic4627	16.902431	-7.635333
ic4628	16.949564	-40.450972
ic4629	16.936108	-16.709889
ic4630	16.919328	26.662917
ic4631	17.183342	-77.603556
ic4632	16.975592	22.915556
ic4633	17.229733	-77.536194
ic4634	17.025997	-21.825972
ic4635	17.260886	-77.489528
ic4636	16.985228	47.195417
ic4637	17.086339	-40.886361
ic4638	17.020472	33.513194
ic4639	17.048542	22.930028
ic4640	17.399542	-80.064083
ic4641	17.402867	-80.147417
ic4642	17.195894	-55.399
ic4643,ngc6301	17.142428	42.339111
ic4644	17.41025	-73.940111
ic4645	17.245314	43.104111
ic4646	17.398108	-59.999389
ic4647	17.434372	-80.195111
ic4648	17.269453	43.862583
ic4650	17.263169	57.301889
ic4651	17.41365	-49.93825
ic4652	17.440742	-59.728306
ic4653	17.451994	-60.879583
ic4654	17.618858	-74.381444
ic4655	17.576561	-60.721333
ic4656	17.628853	-63.729667
ic4657	17.545194	-17.524833
ic4658	17.603003	-59.584917
ic4659	17.570064	-17.928028
ic4660	17.36255	75.8485
ic4661	17.850767	-74.032389
ic4662	17.785797	-64.64175
ic4663	17.757833	-44.904861
ic4664	17.816275	-63.254528
ic4665	17.774217	5.648722
ic4666	17.767322	55.775583
ic4667	17.771933	55.875639
ic4668	17.783169	57.400694
ic4669	17.786936	61.434222
ic4670	17.918611	-21.74425
ic4671	17.918861	-10.285917
ic4672	18.037419	-62.8325
ic4673	18.055111	-27.106111
ic4674	18.136967	-62.3955
ic4675	18.052967	-9.259472
ic4676	18.048053	11.823139
ic4677	17.971047	66.633278
ic4678	18.109297	-23.954444
ic4679	18.190136	-56.254389
ic4680	18.2249	-64.476722
ic4681	18.138889	-23.432028
ic4682	18.273808	-71.581306
ic4683	18.150258	-26.390944
ic4684,lbn34	18.152344	-23.435444
ic4685	18.154861	-23.98725
ic4686	18.2274	-57.732528
ic4687	18.227675	-57.725361
ic4688	18.136633	11.712222
ic4689	18.227856	-57.748194
ic4690,lbn43,ngc6589	18.282047	-19.777083
ic4691	18.146028	11.830083
ic4692	18.247214	-58.693778
ic4693	18.153008	17.347889
ic4694	18.257347	-58.208917
ic4695	18.289853	-58.925472
ic4696	18.338308	-64.734083
ic4697	18.207475	25.427194
ic4698	18.349981	-63.347944
ic4699	18.309108	-45.983083
ic4700,lbn46,ngc6590,ngc6595	18.284719	-19.866056
ic4701,lbn55	18.276594	-16.648278
ic4702	18.384394	-59.238944
eaglenebula,ic4703,starqueen	18.315617	-13.845389
ic4704	18.4649	-71.609861
ic4705	18.469533	-71.693944
ic4706	18.326928	-16.031278
ic4707	18.331642	-16.00925
ic4708	18.229503	61.157278
ic4709	18.405386	-56.369167
ic4710	18.477214	-66.982278
ic4711	18.468561	-64.944472
ic4712	18.518589	-71.693667
ic4713	18.499817	-67.224389
ic4714	18.515486	-66.65175
ic4715,m24,smallsgrstarcloud	18.282256	-18.514556
ic4716	18.545844	-56.962
ic4717	18.554792	-57.975722
ic4718	18.563933	-60.129111
ic4719	18.553206	-56.732194
ic4720	18.559028	-58.405361
ic4721	18.573544	-58.496611
ic4722	18.575425	-57.792778
ic4723	18.598961	-63.376667
ic4724	18.644522	-70.125667
ic4725,m25	18.529658	-19.114944
ic4726	18.616336	-62.854333
ic4727	18.632239	-62.700667
ic4728	18.6325	-62.530917
ic4729	18.665675	-67.425694
ic4730	18.647269	-63.349917
ic4731	18.645272	-62.943028
ic4732	18.565167	-22.644722
ic4733	18.443939	64.967417
ic4734	18.640472	-57.490444
ic4735	18.663872	-62.956028
ic4736	18.644392	-57.893278
ic4737	18.666222	-62.597972
ic4738	18.674144	-61.902361
ic4739	18.680828	-61.901556
ic4740	18.716828	-68.359944
ic4741	18.695397	-63.948194
ic4742	18.697936	-63.862083
ic4743	18.691431	-61.772222
ic4744	18.698581	-63.223861
ic4745	18.709967	-64.942917
ic4746	18.765142	-72.668222
ic4747	18.765928	-72.630028
ic4748	18.712767	-64.072667
ic4749	18.713747	-63.208417
ic4750	18.717411	-62.971472
ic4751	18.722039	-62.112278
ic4752	18.729647	-64.082111
ic4753	18.725728	-62.107944
ic4754	18.733397	-61.990056
ic4755	18.750319	-63.692222
ic4756	18.647642	5.462167
ic4757	18.732153	-57.167556
ic4758	18.771742	-65.756667
ic4759	18.761389	-63.085278
ic4760	18.762764	-62.958361
ic4761	18.732111	-52.853028
ic4762	18.541258	67.858028
ic4763,ngc6679	18.558472	67.137306
ic4764	18.785436	-63.484556
ic4765	18.788314	-63.331333
ic4766	18.793269	-63.292167
ic4767	18.794925	-63.405667
ic4768	18.691164	-5.534833
ic4769	18.795569	-63.157
ic4770	18.802869	-63.383444
ic4771	18.806622	-63.247667
ic4772	18.665694	40.026389
ic4773	18.855783	-69.92475
ic4774	18.802958	-57.935694
ic4775	18.807303	-57.183722
ic4776	18.764083	-33.343056
ic4777	18.803139	-53.147611
ic4778	18.833436	-61.7195
ic4779	18.841786	-63.012889
ic4780	18.832247	-59.252861
ic4781	18.860456	-62.792611
ic4782	18.848575	-55.491222
ic4783	18.859269	-58.813167
ic4784	18.880006	-63.259611
ic4785	18.882008	-59.255417
ic4786	18.879047	-56.694611
ic4787	18.934628	-68.682361
ic4788	18.911394	-63.452389
ic4789	18.938469	-68.567111
ic4790	18.942281	-64.928917
ic4791	18.816994	19.331111
ic4792	18.928267	-56.403806
ic4793	18.948778	-61.399778
ic4794	18.952675	-62.090944
ic4795	18.954544	-61.609083
ic4796	18.941067	-54.213944
ic4797	18.941578	-54.305778
ic4798	18.972469	-62.118417
ic4799	18.982386	-63.930972
ic4800	18.978756	-63.139222
ic4801	18.993997	-64.675139
ic4802	18.918636	-22.698306
ic4803	19.011075	-62.065139
ic4804	19.018717	-61.833333
ic4805	19.033728	-63.047639
ic4806	19.025192	-57.532056
ic4807	19.038239	-56.931194
ic4808	19.018783	-45.313722
ic4809	19.068161	-62.194083
ic4810	19.049919	-56.159722
ic4811	19.095742	-67.133833
ic4812	19.017675	-37.060333
ic4813	19.094919	-66.522056
ic4814	19.083025	-58.579389
ic4815	19.114058	-61.701361
ic4816	19.0307	-13.161833
ic4817	19.103431	-56.159361
ic4818	19.100844	-55.136833
ic4819	19.118694	-59.466944
ic4820	19.153753	-63.4655
ic4821	19.158892	-55.017306
ic4822	19.245969	-72.441139
ic4823	19.204375	-63.975861
ic4824	19.220575	-62.088278
ic4825	19.287675	-72.74875
ic4826	19.205889	-57.202306
ic4827	19.222567	-60.860167
ic4828	19.227969	-62.082611
ic4829	19.209361	-56.54025
ic4830	19.230156	-59.294361
ic4831	19.245511	-62.272611
ic4832	19.234408	-56.610722
ic4833	19.261431	-62.329944
ic4834	19.275369	-64.006167
ic4835	19.257633	-58.238
ic4836	19.271647	-60.200333
ic4837	19.254067	-54.661417
ic4837a	19.254492	-54.1325
ic4838	19.279475	-61.6145
ic4839	19.259478	-54.626694
ic4840	19.264358	-56.209083
ic4841	19.345231	-72.226778
ic4842	19.323464	-60.64425
ic4843	19.322692	-59.308861
ic4844	19.3174	-56.027167
ic4845	19.339581	-60.389167
ic4846	19.274528	-9.043611
ic4847	19.392225	-65.506667
ic4848	19.381825	-56.780806
ic4849	19.426664	-62.932722
ic4850	19.340025	-0.133556
ic4851	19.424844	-57.670444
ic4852	19.440372	-60.336056
ic4853	19.513142	-71.070028
ic4854,ic4855	19.455875	-59.315444
ic4856	19.458481	-54.908528
ic4857,ic4858	19.47755	-58.767917
ic4859	19.512961	-66.314722
ic4860	19.524308	-67.369028
ic4861	19.487978	-57.574972
ic4862	19.527875	-67.322889
ic4863	19.464358	-36.216889
ic4864	19.668381	-77.558167
ic4865	19.513983	-46.698444
ic4866	19.576319	-61.145778
ic4868	19.559278	-45.892694
ic4869	19.600647	-61.027861
ic4870	19.627111	-65.811833
ic4871,ic4872	19.595064	-57.519222
ic4873	19.581858	-46.135833
ic4874	19.605983	-47.265944
ic4875	19.627358	-52.075722
ic4876	19.628547	-52.84275
ic4877	19.632192	-51.991389
ic4878	19.647242	-58.226444
ic4879	19.660125	-52.368778
ic4880	19.675253	-56.410167
ic4881	19.673894	-55.857722
ic4882	19.673142	-55.196917
ic4883	19.700147	-55.545528
ic4884	19.711417	-58.128472
ic4885	19.731122	-60.65175
ic4886	19.720708	-51.8075
ic4887	19.805914	-69.587194
ic4888	19.747844	-54.456639
ic4889,ic4891	19.754208	-54.344139
ic4890	19.75985	-56.545444
ic4892	19.825447	-70.227444
ic4893	19.8426	-72.51
ic4894	19.783086	-51.8465
barnardsgalaxy,ic4895,ngc6822	19.749372	-14.803444
ic4896	19.818031	-58.981444
ic4897	19.822139	-51.868
ic4898	19.796161	-33.320583
ic4899	19.907431	-70.58975
ic4900	19.839472	-51.345833
ic4901	19.906536	-58.713556
ic4902	19.906697	-56.379083
ic4903	19.970394	-70.453417
ic4904	19.977447	-70.184194
ic4905	19.934964	-61.221083
ic4906	19.946556	-60.468083
ic4907	19.936961	-52.453972
ic4908	19.949075	-55.791722
ic4909	19.946	-50.05575
ic4910	19.963053	-56.86325
ic4911	19.961619	-51.986472
ic4912	20.113803	-77.3575
ic4913	19.946567	-37.328361
ic4914	19.965697	-50.1315
ic4915	19.975539	-52.642222
ic4916	19.971992	-50.272111
ic4917	19.981881	-52.273194
ic4918	19.986997	-52.275139
ic4919	20.002514	-55.373389
ic4920	20.002447	-53.383778
ic4921	20.055444	-67.826861
ic4922	19.991492	-40.363083
ic4923	20.015936	-52.631667
ic4924	19.997619	-41.546056
ic4925	20.019408	-52.865833
ic4926	20.003375	-38.578583
ic4927	20.030411	-53.91775
ic4928	20.17	-77.308972
ic4929	20.111583	-71.683556
ic4930	20.040683	-54.308583
ic4931	20.013989	-38.575056
ic4932	20.037633	-52.846167
ic4933	20.058067	-54.979944
ic4934	20.120792	-69.479194
ic4935	20.076144	-57.598167
ic4936	20.097833	-61.428528
ic4937	20.088217	-56.256194
ic4938	20.10325	-60.211611
ic4939	20.119733	-60.738806
ic4940	20.09545	-44.699944
ic4941	20.116281	-53.652306
ic4942	20.113717	-52.609917
ic4943	20.10785	-48.375611
ic4944	20.119122	-54.446889
ic4945,ngc6876a	20.188014	-71.012944
ic4946	20.399464	-43.995278
ic4947	20.125486	-53.142444
ic4948,ngc6902	20.407817	-43.653528
ic4949,ngc6861	20.122078	-48.370222
ic4950	20.140933	-56.161833
ic4951	20.158825	-61.850472
ic4952	20.143792	-55.453667
ic4953	20.166644	-62.792222
ic4954,lbn153	20.079172	29.252806
ic4955	20.081264	29.192611
ic4956	20.192017	-45.593222
ic4957	20.159897	-55.709306
ic4958	20.259817	-72.711194
ic4959	20.182561	-53.089694
ic4960	20.256633	-70.53775
ic4961	20.191275	-53.125111
ic4962	20.278469	-71.129556
ic4963	20.201525	-55.245889
ic4964	20.289981	-73.885639
ic4965	20.207589	-56.826778
ic4966	20.204561	-53.619194
ic4967	20.273097	-70.564694
ic4968	20.247286	-64.798389
ic4969	20.215639	-53.920056
ic4970	20.282597	-70.74975
ic4971	20.284128	-70.620972
ic4972	20.2952	-70.915111
ic4973	20.242814	-58.371111
ic4974	20.257361	-61.860278
ic4975	20.234172	-52.721778
ic4976	20.261406	-61.875139
ic4977	20.198111	-21.636639
ic4978	20.243792	-54.421972
ic4979	20.244956	-53.458694
ic4980	20.258036	-57.912694
ic4981	20.327556	-70.848528
ic4982	20.339122	-71.007833
ic4983	20.268319	-52.086528
ic4984	20.271514	-52.703722
ic4985	20.345561	-70.987
ic4986	20.286569	-55.036389
ic4987	20.288717	-52.279556
ic4988	20.362847	-69.387639
ic4989	20.323247	-58.551472
ic4990	20.357108	-66.890861
ic4991	20.306467	-41.050167
ic4992	20.391069	-71.564917
ic4993	20.365656	-66.985389
ic4994	20.329033	-53.447361
ic4995	20.333047	-52.621972
ic4996	20.275908	37.555278
ic4997	20.335778	16.731667
ic4998,ic5018	20.369606	-38.308333
ic4999	20.398983	-26.014944
ic5000,ngc6901	20.372642	6.429861
ic5001	20.438903	-54.774722
ic5002	20.444414	-54.799694
ic5003,ic5029,ic5039,ic5046	20.72065	-29.853389
ic5004,ngc6923	20.527519	-30.831889
ic5005	20.422281	-25.829278
ic5006	20.396367	6.449167
ic5007,ic5030,ic5041,ic5047	20.726236	-29.703639
ic5008	20.545842	-72.694722
ic5009	20.542875	-72.167556
ic5010	20.507411	-66.097361
ic5011,ic5013	20.476061	-36.027111
ic5012	20.492217	-56.743111
ic5014	20.5877	-73.452611
ic5015,ngc6925	20.572381	-31.980889
ic5016	20.593589	-72.911139
ic5017	20.534397	-57.587694
ic5019	20.513081	-36.076944
ic5020	20.510692	-33.485556
ic5021	20.559456	-54.520778
ic5022	20.685039	-76.450139
ic5023	20.636311	-67.184639
ic5024	20.669317	-71.107694
ic5025	20.749744	-76.984694
ic5026	20.807792	-78.06925
ic5027	20.685814	-55.472111
ic5028	20.722786	-65.647806
ic5031	20.755631	-67.539333
ic5032	20.756119	-67.551889
ic5033	20.731969	-57.334278
ic5034	20.728242	-57.030306
ic5035	20.737347	-57.127528
ic5036	20.743828	-57.626778
ic5037	20.760903	-58.449778
ic5038	20.781014	-65.016806
ic5040	20.872114	-76.686556
ic5042	20.796117	-65.084306
ic5043	20.777294	-56.983667
ic5044	20.844872	-71.899417
ic5045	20.847253	-71.909778
ic5048	20.861289	-71.800778
ic5049	20.789844	-38.415694
ic5049a	20.789783	-38.413167
ic5049b	20.789953	-38.418278
ic5050	20.754181	-5.622778
ic5051	20.872958	-71.789889
ic5052	20.868214	-69.201639
ic5053	20.893392	-71.141222
ic5054	20.89595	-71.02475
ic5055	20.882547	-68.445667
ic5056	20.816528	-39.180917
ic5057	20.787083	0.322111
ic5058,ngc6965	20.788992	0.484056
ic5059	20.853744	-57.688667
ic5060	20.912961	-71.636472
ic5061	20.793653	0.335667
ic5062	20.802833	-8.35975
ic5063	20.867317	-57.068778
ic5064	20.8773	-57.232444
ic5065	20.862722	-29.847278
ic5066	20.950839	-73.14725
ic5067	20.797272	44.366972
ic5068,lbn328	20.8416	42.477694
ic5069	21.003569	-71.811694
ic5070,lbn350,pelicannebula	20.8502	44.4015
ic5071	21.02215	-72.642722
ic5072	21.03245	-72.988472
ic5073	21.055517	-72.687889
ic5074	21.016794	-63.152667
ic5075	21.07725	-71.867861
ic5076,lbn394	20.92595	47.395556
ic5077	21.148322	-73.640806
ic5078	21.042019	-16.818306
ic5079	21.095558	-56.23025
ic5080	21.042519	19.213611
ic5081	21.050342	19.18925
ic5082,ngc7010	21.077639	-12.338389
ic5083	21.064306	11.763639
ic5084	21.154131	-63.290028
ic5085	21.224325	-74.103056
ic5086	21.142225	-29.769056
ic5087	21.239292	-73.773833
ic5088	21.157433	-22.878583
ic5089	21.181814	-3.862778
ic5090	21.1918	-2.032556
ic5091	21.293617	-70.652944
ic5092	21.270694	-64.464667
ic5093	21.312883	-70.622389
ic5094	21.297083	-66.427667
ic5095	21.289511	-59.947556
ic5096	21.305983	-63.760667
ic5097	21.249467	4.484111
ic5098	21.250383	4.493611
ic5099	21.363625	-70.983361
ic5100	21.362072	-65.933361
ic5101	21.365492	-65.836056
ic5102	21.437072	-73.310083
ic5103	21.486819	-74.070167
ic5104	21.358125	21.241972
ic5105	21.406114	-40.537722
ic5106	21.477258	-70.834583
ic5107	21.470803	-65.735528
ic5108	21.547639	-72.659694
ic5109	21.561864	-74.112
ic5110	21.512053	-60.001833
ic5111	21.469656	2.47375
ic5113	21.494303	6.818
ic5114,ngc7091	21.568872	-36.653722
ic5115	21.515914	11.7635
ic5116	21.618194	-70.982556
ic5117	21.541936	44.596556
ic5118	21.703833	-71.382694
ic5119	21.565514	21.837917
ic5120,ngc7096a	21.646742	-64.350194
ic5121,ngc7096	21.688689	-63.908694
ic5122	21.662742	-22.406528
ic5123	21.747042	-72.42075
ic5124	21.665331	-22.426944
ic5125	21.697272	-52.773611
ic5126	21.674603	-6.34575
ic5127,ngc7102	21.662358	6.286306
ic5128	21.719936	-38.968278
ic5129	21.796272	-65.387806
ic5130	21.840075	-73.997417
ic5131	21.790364	-34.883667
ic5132	21.711169	66.168444
ic5133	21.713094	66.181139
ic5134	21.7163	66.102833
ic5135,ngc7130	21.805422	-34.95125
ic5136,ngc7135	21.829447	-34.876278
ic5137	21.860406	-65.583667
ic5138	21.889358	-68.953639
ic5139	21.840461	-30.994722
ic5140	21.904453	-67.331389
ic5141	21.888067	-59.493556
ic5142	21.922358	-65.510028
ic5143,ngc7155	21.936036	-49.521944
ic5144	21.902647	15.036833
ic5145	21.906406	15.156833
cocoonnebula,ic5146,lbn424	21.891322	47.266917
ic5147	21.990644	-65.449861
ic5148,ic5150	21.993111	-39.385833
ic5149	21.983067	-27.413917
ic5151	21.981278	3.761472
ic5152	22.044864	-51.296444
ic5153	22.006544	17.863917
ic5154	22.075081	-66.112389
ic5155	22.035072	0.488278
ic5156	22.054131	-33.838444
ic5157	22.0575	-34.941833
ic5158	22.106881	-67.517
ic5159	22.044414	0.319
ic5160	22.051344	10.924861
ic5161	22.094169	9.640167
ic5162	22.134189	-52.713861
ic5163	22.096494	27.0855
ic5164	22.0995	27.047472
ic5165	22.168633	-64.578028
ic5166	22.1019	27.068
ic5167	22.125497	-8.122611
ic5168	22.145983	-27.856472
ic5169	22.169439	-36.088611
ic5170	22.208233	-47.221944
ic5171	22.182417	-46.081472
ic5172	22.165419	12.818056
ic5173	22.244833	-69.366389
ic5173a	22.245714	-69.365389
ic5173b	22.244075	-69.36775
ic5174	22.212408	-38.171389
ic5175	22.213397	-38.127444
ic5176	22.248869	-66.849417
ic5177	22.192853	11.795944
ic5178	22.209264	-22.954056
ic5179,ic5183,ic5184	22.269194	-36.843722
ic5180	22.186669	38.927194
ic5181	22.222694	-46.017611
ic5182	22.268081	-65.454722
ic5185	22.295458	-65.857472
ic5186	22.312922	-36.801583
ic5187	22.304936	-59.606972
ic5188	22.307333	-59.641333
ic5189	22.270597	-5.004306
ic5190	22.316858	-59.882722
ic5191	22.250686	37.300389
ic5192	22.2539	37.271028
ic5193	22.262097	37.242833
ic5194	22.285592	-15.945694
ic5195	22.261547	37.302778
ic5196	22.336461	-65.404611
ic5197	22.330394	-60.136444
ic5198,ngc7246	22.295189	-15.571278
ic5199	22.325894	-37.533806
ic5200	22.370928	-65.766333
ic5201	22.349289	-46.035861
ic5202	22.382131	-65.802889
ic5203	22.376194	-59.773222
ic5204,ngc7300	22.516642	-14.003528
ic5205	22.379878	-59.787056
ic5206	22.401283	-66.857833
ic5207	22.391514	-60.564972
ic5208	22.409519	-65.227417
ic5209	22.385861	-37.993278
ic5210	22.375308	-18.869694
ic5211	22.378628	-18.880222
ic5212	22.391739	-38.037639
ic5213	22.417997	-60.476694
ic5214	22.395058	-27.469806
ic5215	22.449475	-65.982194
ic5216	22.412436	-18.087611
ic5217	22.398806	50.966667
ic5218	22.468272	-60.394861
ic5219	22.478817	-65.893722
ic5220	22.467425	-59.723444
ic5221	22.482697	-65.904583
ic5222	22.49855	-65.661361
ic5223	22.495769	7.98875
ic5224	22.508375	-45.996194
ic5225,ngc7294	22.535572	-25.397778
ic5226	22.541725	-25.661972
ic5227	22.567697	-64.697667
ic5228,ngc7302	22.539944	-14.120528
ic5229	22.580661	-61.381361
ic5230	22.594492	-61.547694
ic5231	22.566867	23.338667
ic5232	22.627253	-68.872222
ic5233	22.609133	25.763194
ic5234	22.669847	-65.82525
ic5235	22.690408	-66.580306
ic5236	22.691706	-66.618
ic5237,ngc7361	22.704975	-30.057667
ic5238	22.691603	-60.757917
ic5239	22.518661	-38.026528
ic5240	22.697883	-44.767167
ic5241	22.694036	2.639944
ic5242	22.687558	23.406917
ic5243	22.690164	23.374639
ic5244	22.737153	-64.043389
ic5245	22.748992	-65.357917
ic5246	22.777639	-64.897972
ic5247	22.780597	-65.273889
ic5248	22.745208	-0.3395
ic5249	22.785078	-64.832028
ic5250	22.789006	-65.058722
ic5250a	22.788194	-65.059722
ic5250b	22.789489	-65.0585
ic5251	22.752953	11.158472
ic5252	22.802497	-68.902861
ic5253	22.758033	21.808056
ic5254	22.766808	21.125583
ic5255	22.762789	36.226778
ic5256	22.829392	-68.690667
ic5257	22.871181	-67.419556
ic5258	22.858769	23.080583
ic5259	22.920747	36.671778
ic5260,ngc7404	22.905169	-39.314944
ic5261	22.907011	-20.362889
ic5262	22.922347	-33.887917
ic5263	22.970436	-69.052111
ic5264	22.948067	-36.554167
ic5266	22.972453	-65.129694
ic5267	22.953769	-43.396139
ic5268	22.936936	36.59725
ic5269	22.962128	-36.026222
ic5270	22.965261	-35.858056
ic5271	22.967172	-33.742222
ic5272	22.991972	-65.193528
ic5273	22.99075	-37.702889
ic5274	22.974347	18.91875
ic5275	22.977628	18.862528
ic5276	22.977708	18.819917
ic5277	23.033125	-65.197889
ic5278	23.0044	-8.178778
ic5279	23.050728	-69.209722
ic5280	23.063931	-65.207861
ic5281	23.039858	27.006389
ic5282	23.046719	21.874361
ic5283	23.055	8.893611
ic5284	23.112853	19.122083
ic5285	23.116372	22.936472
ic5286	23.165419	-68.253111
ic5287	23.155631	0.7565
ic5288	23.195617	-68.094056
ic5289	23.188044	-32.454278
ic5290	23.214794	-23.469194
ic5291	23.227661	9.241528
ic5292	23.229742	13.687611
ic5293	23.245733	25.140611
ic5294,ngc7552	23.269656	-42.58475
ic5295	23.258094	25.120472
ic5296	23.262161	25.094528
ic5297	23.266233	25.025194
ic5298	23.266861	25.556694
ic5299	23.271986	20.855833
ic5300	23.276136	20.828444
ic5301	23.316508	-69.562111
ic5302	23.326858	-64.568278
ic5303	23.298539	0.264528
ic5304	23.314597	-10.259306
ic5305	23.301728	10.299861
ic5306	23.303147	10.246056
ic5307	23.306119	10.23575
ic5308,ngc7599	23.322539	-42.256833
ic5309	23.319903	8.109306
ic5310	23.346567	-22.149361
ic5311	23.343819	17.274139
ic5312	23.349533	19.318028
ic5313,ngc7632	23.366917	-42.4805
ic5314	23.352372	19.311222
ic5315	23.355069	25.385194
ic5316	23.365031	21.202556
ic5317	23.3913	21.163528
ic5318,ngc7646	23.401933	-11.860694
ic5319	23.4136	13.996528
ic5320	23.472769	-67.760278
ic5321	23.438953	-17.956389
ic5322	23.475225	-67.761333
ic5323	23.460269	-67.815472
ic5324	23.471597	-67.821361
ic5325	23.478731	-41.333472
ic5326	23.4931	-28.831167
ic5328	23.554572	-45.015972
ic5329	23.552664	21.237306
ic5330	23.557314	-2.883139
ic5331	23.556894	21.130056
ic5332	23.574303	-36.101083
ic5333,ngc7697	23.581383	-65.396028
ic5334	23.576783	-4.53425
ic5335	23.596492	-67.396972
ic5336	23.605469	21.098111
ic5337	23.606953	21.150556
ic5338	23.608453	21.146
ic5339	23.634797	-68.442056
ic5340	23.642319	-4.854611
ic5341	23.640783	26.985111
ic5342	23.644111	27.011361
ic5343	23.656214	-22.497167
ic5344	23.6544	-4.96675
ic5345	23.658953	-22.413333
ic5346	23.685092	24.949806
ic5347	23.693531	24.885778
ic5348,ngc7744	23.749789	-42.910917
ic5349	23.773008	-28.005111
ic5350	23.787397	-27.957722
ic5351	23.788592	-2.3135
ic5352	23.788861	-2.280667
ic5353	23.791275	-28.109472
ic5354	23.791206	-28.136
ic5355	23.787581	32.78275
ic5356	23.789942	-2.35125
ic5357	23.789719	-2.300667
ic5358	23.795844	-28.14075
ic5359	23.79385	-2.316667
ic5360	23.798258	-37.058667
ic5361,ngc7761	23.858025	-13.381583
ic5362,ic5363	23.860203	-28.365056
ic5364	23.940278	-29.023333
ic5365	23.959608	-37.024889
ic5366	23.961219	52.791639
ic5367	23.977475	22.449083
ic5369	23.997372	32.702361
ic5370	0.00255	32.738389
ic5371	0.004106	32.832
ic5372	0.004517	32.792611
ic5373	0.008003	32.782361
ic5374	0.017922	4.500194
ic5375	0.017992	4.540611
ic5376	0.022158	34.525722
ic5377	0.034833	16.590278
ic5378	0.043833	16.648056
ic5379	0.044639	16.600278
ic5380	0.0471	-66.186528
ic5381	0.053131	15.965722
ic5382	0.057278	-65.196667
ic5383	0.063556	16.014167
ic5384,ngc7813	0.0692	-11.983889
ic5385	0.106583	-0.076667
ic5386,ngc7832	0.107906	-3.716139
ngc1	0.121067	27.708083
ngc2	0.121419	27.678361
ngc3	0.121333	8.301639
ngc4	0.123447	8.373778
ngc5	0.130242	35.362306
ngc20,ngc6	0.159083	33.308667
ngc7	0.139156	-29.915
ngc8	0.145917	23.838889
ngc9	0.148528	23.816972
ngc10	0.142928	-33.858333
ngc11	0.145139	37.447917
ngc12	0.145764	4.612528
ngc13	0.146589	33.433333
ngc14	0.146222	15.815556
ngc15	0.150686	21.624528
ngc16	0.151192	27.729417
ngc17,ngc34	0.185153	-12.107306
ngc18	0.156417	27.732083
ngc19	0.178019	32.983083
ngc21,ngc29	0.179694	33.352833
ngc22	0.163386	27.832306
ngc23	0.164836	25.923778
ngc24	0.165706	-24.963139
ngc25	0.166467	-57.020833
ngc26	0.173853	25.831833
ngc27	0.175769	28.99625
ngc28	0.173678	-56.989139
ngc30	0.180775	21.976972
ngc31	0.177331	-56.9865
ngc32	0.181553	18.796
ngc33	0.1824	3.675917
ngc35	0.186244	-12.020917
ngc36	0.189528	6.389361
ngc37	0.189703	-56.957333
ngc38	0.196386	-5.586278
ngc39	0.205239	31.061083
bowtienebula,ngc40	0.216953	72.521944
ngc41	0.213325	22.023389
ngc42	0.215653	22.100306
ngc43	0.216875	30.915278
ngc44	0.220389	31.28625
ngc45	0.234442	-23.182083
ngc46	0.236072	5.987694
ngc47,ngc58	0.241844	-7.167444
ngc48	0.233942	48.234861
ngc49	0.239564	48.246611
ngc50	0.245714	-7.345083
ngc51	0.243033	48.255694
ngc52	0.244475	18.582028
ngc53	0.245236	-60.32875
ngc54	0.252131	-7.106722
ngc55	0.248222	-39.196639
ngc56	0.255739	12.444528
ngc57	0.258575	17.328528
ngc59	0.256981	-21.444389
ngc60	0.266178	-0.303528
ngc61	0.273389	-6.319444
ngc61a	0.273428	-6.321917
ngc61b	0.273353	-6.318861
ngc62	0.284839	-13.487111
ngc63	0.295978	11.450333
ngc64	0.291769	-6.824611
ngc65	0.316308	-22.880361
ngc66	0.318039	-22.936389
ngc67	0.303386	30.055528
ngc68	0.305136	30.07175
ngc69	0.305697	30.039972
ngc71	0.30655	30.06325
ngc72	0.307881	30.040694
ngc72a	0.309528	30.036389
ngc73	0.310836	-15.32225
ngc74	0.313706	30.061972
ngc75	0.323981	6.449361
ngc76	0.327164	29.933861
ngc77	0.333792	-22.532111
ngc78	0.340722	0.829722
ngc78a	0.340497	0.826333
ngc78b	0.340975	0.833556
ngc79	0.350792	22.566583
ngc80	0.353014	22.357194
ngc81	0.353686	22.382889
ngc82	0.354875	22.460361
ngc83	0.356222	22.433611
ngc84	0.355903	22.619694
ngc85	0.357092	22.511778
ngc85b	0.358056	22.505833
ngc86	0.357936	22.556417
ngc87	0.353964	-48.628222
ngc88	0.356144	-48.640167
ngc89	0.356767	-48.665306
ngc90	0.364278	22.4
ngc91	0.364367	22.368361
ngc92	0.358806	-48.62475
ngc93	0.367564	22.408083
ngc94	0.370425	22.483056
ngc95	0.370428	10.491583
ngc96	0.371586	22.54625
ngc97	0.375	29.745361
ngc98	0.380428	-45.269
ngc99	0.399831	15.770417
ngc100	0.400789	16.486389
ngc101	0.398503	-32.536167
ngc102	0.410147	-13.956361
ngc103	0.421222	61.323472
47tuccluster,ngc104	0.401489	-72.081444
ngc105	0.421328	12.883861
ngc106	0.412153	-5.14875
ngc107	0.428389	-8.282806
ngc108	0.433258	29.212056
ngc109	0.4374	21.807306
ngc110	0.456947	71.391528
ngc111	0.444003	-2.624972
ngc112	0.446869	31.703306
ngc113	0.448511	-2.500889
ngc114	0.449508	-1.78625
ngc115	0.446189	-33.677083
ngc116	0.451453	-7.66825
ngc117	0.453075	1.333722
ngc118	0.454506	-1.780139
ngc119	0.449336	-56.978056
ngc120	0.458356	-1.513472
ngc121	0.446736	-71.535667
ngc122	0.460647	-1.640472
ngc123	0.461108	-1.627639
ngc124	0.464544	-1.810194
ngc125	0.480608	2.838861
ngc126	0.485583	2.811111
ngc127	0.486769	2.872694
ngc128	0.487517	2.864056
ngc129	0.499497	60.211167
ngc130	0.488486	2.870444
ngc131	0.494033	-33.25975
ngc132	0.502975	2.093444
ngc133	0.521378	63.352611
ngc134	0.506103	-33.244028
ngc136	0.525219	61.50925
ngc137	0.516139	10.208417
ngc138	0.516456	5.15975
ngc139	0.518444	5.07875
ngc140	0.522353	30.7925
ngc141	0.521511	5.17975
ngc142	0.518911	-22.618667
ngc143	0.521006	-22.559944
ngc144	0.522408	-22.645722
ngc145	0.529372	-5.152639
ngc146	0.551094	63.309
ngc147	0.553367	48.50875
ngc148	0.570972	-31.786
ngc149	0.563961	30.723417
ngc150	0.570967	-27.803583
ngc151,ngc153	0.567442	-9.705333
ngc152	0.547906	-73.120389
ngc154	0.572075	-12.656306
ngc155	0.5778	-10.7665
ngc156	0.576617	-8.340056
ngc157	0.579656	-8.396444
ngc158	0.584889	-8.345722
ngc159	0.576536	-55.789972
ngc160	0.601128	23.957889
ngc161	0.592761	-2.848694
ngc162	0.602572	23.962417
ngc163	0.599953	-10.121694
ngc164	0.609142	2.749778
ngc165	0.608033	-10.106167
ngc166	0.596883	-13.610639
ngc167	0.589747	-23.375
ngc168	0.610739	-22.5935
ngc169	0.614333	23.990917
ngc170	0.612728	1.886472
ngc171,ngc175	0.622647	-19.93425
ngc172	0.620447	-22.587028
ngc173	0.620131	1.94225
ngc174	0.616372	-29.477833
ngc176	0.599408	-73.166389
ngc177	0.626206	-22.54925
ngc179	0.629522	-17.849472
ngc180	0.632694	8.635194
ngc181	0.639781	29.472583
ngc182	0.636772	2.728556
ngc183	0.641497	29.511222
ngc184	0.643272	29.447611
ngc185	0.649436	48.337389
ngc186	0.640361	3.166444
ngc187	0.658447	-14.656306
ngc188	0.790981	85.269639
ngc189	0.659917	61.094472
ngc190	0.648528	7.059722
ngc191	0.649844	-9.002611
ngc192	0.653731	0.864333
ngc193	0.655164	3.331111
ngc194	0.655117	3.037444
ngc195	0.659942	-9.194528
ngc196	0.654956	0.91275
ngc197	0.655219	0.891917
ngc198	0.656383	2.797917
ngc199	0.659214	3.138528
ngc200	0.659689	2.887444
ngc201	0.659672	0.859889
ngc202	0.661069	3.536278
ngc203,ngc211	0.660981	3.442889
ngc204	0.662297	3.299583
m110,ngc205	0.6728	41.685306
ngc206	0.675361	40.739278
ngc207	0.661308	-14.237083
ngc208	0.67155	2.7565
ngc209	0.651	-18.608278
ngc210	0.676394	-13.872806
ngc212	0.670369	-56.153028
ngc213	0.686111	16.469389
ngc214	0.691119	25.499444
ngc215	0.680242	-56.214056
ngc216	0.690875	-21.045444
ngc217	0.692747	-10.021417
ngc218	0.775553	36.325611
ngc219	0.703142	0.904556
ngc220	0.674969	-73.403972
m32,ngc221	0.711619	40.865278
ngc222	0.678808	-73.385694
andromedagalaxy,m31,ngc224	0.712319	41.269056
ngc225	0.726772	61.766944
ngc226	0.715011	32.580972
ngc227	0.710231	-1.528778
ngc228	0.715142	23.503056
ngc229	0.717956	23.509111
ngc230	0.707547	-23.628806
ngc231	0.685119	-73.352417
ngc232	0.712728	-23.561361
ngc233	0.726822	30.587
ngc234	0.725664	14.342556
ngc235	0.714778	-23.543333
ngc235a	0.714669	-23.541028
ngc235b	0.714889	-23.545556
ngc236	0.724317	2.958194
ngc237	0.7244	-0.124917
ngc238	0.723819	-50.182833
ngc239	0.743753	-3.75925
ngc240	0.750536	6.113361
ngc241	0.725425	-73.440472
ngc242	0.72605	-73.446306
ngc243	0.766908	29.9595
ngc244	0.762897	-15.596889
ngc245	0.768164	-1.723389
ngc246	0.784267	-11.871944
ngc247	0.785708	-20.760389
ngc247a	0.79115	-20.397639
ngc247b	0.793097	-20.428694
ngc247c	0.793808	-20.452806
ngc247d	0.793608	-20.486
ngc248	0.756678	-73.379806
ngc249	0.759128	-73.080083
ngc250	0.787781	7.910028
ngc251	0.798342	19.596833
ngc252	0.800417	27.623639
ngc253,sculptorfilament,silvercoin	0.792533	-25.288222
ngc254	0.791003	-31.42175
ngc255	0.796475	-11.468694
ngc256	0.764814	-73.506833
ngc257	0.800419	8.297083
ngc258	0.803553	27.657194
ngc259	0.800914	-2.775333
ngc260	0.809625	27.692444
ngc261	0.774419	-73.103639
ngc262	0.813094	31.956972
ngc263	0.813464	-13.107389
ngc264	0.805817	-38.234361
ngc265	0.786156	-73.477167
ngc266	0.829944	32.277722
ngc267	0.800806	-73.274028
ngc268	0.835989	-5.193722
ngc269	0.806119	-73.531528
ngc270	0.842367	-8.651639
ngc271	0.844961	-1.91025
ngc272	0.856989	35.82175
ngc273	0.846792	-6.885694
ngc274	0.850517	-7.056944
ngc275	0.851167	-7.066667
ngc277	0.854786	-8.596833
ngc278	0.867864	47.5505
ngc279	0.869153	-2.218444
ngc280	0.875072	24.350583
ngc282	0.878375	30.639056
ngc283	0.887003	-13.163889
ngc284	0.890075	-13.158861
ngc285	0.891636	-13.160722
ngc286	0.891772	-13.112778
ngc287	0.891192	32.482306
ngc288	0.879847	-26.589889
ngc289	0.878433	-31.205833
ngc290	0.853939	-73.161528
ngc291	0.891644	-8.767806
ngc292,smallmagellaniccloud	0.879106	-72.828611
ngc293	0.904433	-7.235472
ngc294	0.884642	-73.380361
ngc295	0.9923	31.798056
ngc296	0.918753	31.542278
ngc297	0.916372	-7.349667
ngc298	0.917319	-7.333083
ngc299	0.890019	-72.197111
ngc300	0.914856	-37.684389
ngc301	0.938431	-10.673889
ngc302	0.940364	-10.663222
ngc303	0.915197	-16.654611
ngc304	0.935006	24.126889
ngc305	0.939144	12.065111
ngc306	0.903939	-72.242333
ngc307	0.942383	-1.771944
ngc308	0.942839	-1.783917
ngc309	0.945183	-9.913861
ngc310	0.946661	-1.765778
ngc311	0.959092	30.28075
ngc312	0.937758	-52.782694
ngc313	0.962678	30.366083
ngc314	0.947892	-31.962972
ngc315	0.963578	30.352444
ngc316	0.964569	30.354306
ngc317	0.961028	43.796389
ngc317a	0.960847	43.800778
ngc317b	0.961236	43.79225
ngc318	0.968119	30.425528
ngc319	0.949333	-43.838778
ngc320	0.979592	-20.840083
ngc321	0.960897	-5.086194
ngc322	0.952781	-43.727083
ngc323	0.944903	-52.975917
ngc324	0.954106	-40.959111
ngc325	0.963297	-5.112083
ngc326	0.972972	26.865278
ngc327	0.965378	-5.130417
ngc328	0.949325	-52.923917
ngc329	0.967111	-5.071222
ngc330	0.938236	-72.462944
ngc331	0.785239	-2.731139
ngc332	0.980314	7.111306
ngc333	0.980889	-16.470278
ngc333a	0.980919	-16.469194
ngc333b	0.980858	-16.471444
ngc334	0.980503	-35.116028
ngc335	0.988828	-18.234667
ngc336	0.967453	-18.384333
ngc337	0.997247	-7.577972
ngc337a	1.026083	-7.58825
ngc338	1.010114	30.668972
ngc339	0.961683	-74.473389
ngc340	1.009689	-6.866583
ngc341	1.012731	-9.185694
ngc342	1.01385	-6.772556
ngc343	0.973314	-23.225222
ngc344	0.973733	-23.229222
ngc345	1.022806	-6.884278
ngc346	0.984733	-72.177111
ngc347	1.026433	-6.733667
ngc348	1.014447	-53.2445
ngc349	1.030764	-6.799806
ngc350	1.032419	-6.795722
ngc351	1.032733	-1.93675
ngc352	1.035892	-4.245472
ngc353	1.040147	-1.958861
ngc354	1.054553	22.342667
ngc355	1.051939	-6.324
ngc356	1.051972	-6.988361
ngc357	1.056078	-6.339222
ngc358	1.086369	62.020444
ngc359	1.071378	-0.764917
ngc360	1.047625	-65.609972
ngc361	1.036156	-71.60475
ngc362	1.053953	-70.848222
ngc363	1.104386	-16.54275
ngc364	1.078008	-0.80275
ngc365	1.071867	-35.121417
ngc366	1.107219	62.228917
ngc367	1.096914	-12.128472
ngc368	1.072789	-43.27675
ngc369	1.085808	-17.759194
ngc370,ngc372	1.112386	32.428694
ngc371	1.058203	-72.056833
ngc373	1.116169	32.308472
ngc374	1.118272	32.795111
ngc375	1.118311	32.348167
ngc376	1.064847	-72.823667
ngc377	1.109672	-20.332556
ngc378	1.103392	-30.178139
ngc379	1.121025	32.520361
ngc380	1.121553	32.482917
ngc381	1.138336	61.583278
ngc382	1.123297	32.403861
ngc383	1.1236	32.412556
ngc384	1.123639	32.292444
ngc385	1.124236	32.319528
ngc386	1.125358	32.362
ngc387	1.12585	32.391111
ngc388	1.129764	32.309972
ngc389	1.141647	39.695444
ngc390	1.131597	32.433111
ngc391	1.122939	0.925944
ngc392	1.13985	33.133611
ngc393	1.143597	39.644306
ngc394	1.140569	33.147972
ngc395	1.085644	-71.990722
ngc396	1.135667	4.530861
ngc397	1.141972	33.109194
ngc398	1.148242	32.514528
ngc399	1.149778	32.634306
ngc400	1.150692	32.732417
ngc401	1.152144	32.759333
ngc402	1.153711	32.80625
ngc403	1.153933	32.752139
ngc404	1.157506	35.718139
ngc405	1.142808	-46.6685
ngc406	1.123625	-69.879167
ngc407	1.176822	33.1265
ngc408	1.180858	33.151278
ngc409	1.159228	-35.805611
ngc410	1.183028	33.151889
ngc411	1.132131	-71.768361
ngc412	1.172356	-20.015806
ngc413	1.208722	-2.793417
ngc414	1.188278	33.112778
ngc415	1.168247	-35.490778
ngc416	1.132917	-72.355056
ngc417	1.184878	-18.148333
ngc418	1.176561	-30.221278
ngc419	1.138103	-72.8835
ngc420	1.202681	32.123167
ngc421	1.204017	32.1235
ngc422	1.157053	-71.767222
ngc423	1.189503	-29.234528
ngc424	1.191008	-38.083472
ngc425	1.217378	38.768361
ngc426	1.213503	-0.290194
ngc427	1.205344	-32.061167
ngc428	1.215475	0.981556
ngc429	1.21595	-0.345
ngc430	1.216647	-0.2525
ngc431	1.234594	33.704194
ngc432	1.196183	-61.527639
ngc433	1.252572	60.125778
ngc434	1.203925	-58.247972
ngc434a	1.208228	-58.2095
ngc435	1.233292	2.071444
ngc436	1.26605	58.817111
ngc437	1.239525	5.926889
ngc438	1.226156	-37.901639
ngc439	1.229794	-31.747139
ngc440	1.213472	-58.282278
ngc441	1.230906	-31.788333
ngc442	1.244069	-1.020639
ngc445	1.247911	1.917444
ngc448	1.254589	-1.626194
ngc449	1.268681	33.089556
ngc450	1.258456	-0.860972
ngc452	1.270786	31.033833
ngc453	1.271506	33.014167
ngc454	1.239592	-55.398694
ngc455	1.266011	5.178694
ngc456	1.228994	-73.290528
ngc457,owlcluster	1.325736	58.290694
ngc458	1.248186	-71.552694
ngc459	1.302275	17.562389
ngc460	1.244056	-73.274194
ngc461	1.289067	-33.840889
ngc462	1.303053	4.226
ngc463	1.316181	16.32575
ngc464	1.324078	34.955417
ngc465	1.261486	-73.334611
ngc466	1.287017	-58.909944
ngc467	1.319481	3.300833
ngc469	1.325819	14.871944
ngc470	1.329125	3.409944
ngc471	1.333219	14.786222
ngc472	1.341303	32.709028
ngc473	1.331964	16.544694
ngc474	1.335192	3.415389
ngc476	1.338861	16.020139
ngc477	1.355658	40.488194
ngc478	1.335914	-22.377389
ngc479	1.354369	3.862278
ngc480	1.342886	-9.880222
ngc481	1.353475	-9.211222
ngc482	1.339006	-40.966111
ngc483	1.365639	33.520972
ngc484	1.326314	-58.524306
ngc485	1.357667	7.018083
ngc486	1.361956	5.346306
ngc487	1.365303	-16.370361
ngc488	1.363014	5.256722
ngc489	1.364972	9.206556
ngc490	1.367464	5.367194
ngc491	1.355675	-34.063278
ngc491a	1.334631	-33.8995
ngc492	1.370433	5.417056
ngc493	1.369164	0.945361
ngc494	1.382056	33.173889
ngc495	1.382222	33.471667
ngc496	1.386556	33.529167
ngc497	1.373272	-0.875194
ngc498	1.386467	33.489361
ngc500	1.377603	5.387278
ngc501	1.389558	33.432972
ngc502	1.382094	9.049194
ngc503	1.391231	33.331722
ngc504	1.391083	33.204444
ngc505	1.382528	9.468889
ngc506	1.393153	33.244667
ngc507	1.394419	33.256056
ngc508	1.394611	33.280278
ngc509	1.390025	9.433556
ngc510	1.398767	33.496889
ngc511	1.391869	11.291
ngc512	1.399944	33.907778
ngc513	1.407458	33.799444
ngc514	1.401083	12.917389
ngc515	1.410722	33.472778
ngc516	1.402242	9.551694
ngc517	1.412167	33.429444
ngc518	1.4049	9.330944
ngc519	1.407956	-1.64125
ngc520	1.409742	3.792417
ngc521	1.409383	1.731389
ngc522	1.412736	9.994639
ngc523,ngc537	1.422425	34.024944
ngc524	1.413256	9.538833
ngc525	1.414697	9.703333
ngc526	1.399583	-35.1225
ngc526a	1.398442	-35.065528
ngc526b	1.399189	-35.069278
ngc527	1.399478	-35.115056
ngc527b	1.399817	-35.127361
ngc528	1.426	33.671667
ngc529	1.427889	34.713333
ngc531	1.438583	34.753889
ngc532	1.421483	9.264111
ngc533	1.425378	1.759111
ngc534	1.412397	-38.129083
ngc535	1.425319	-1.408139
ngc536	1.439383	34.703028
ngc538	1.423903	-1.550639
ngc539,ngc563	1.422703	-18.163861
ngc540	1.452472	-20.036639
ngc541	1.428975	-1.379583
ngc542	1.441917	34.675278
ngc543	1.430553	-1.292806
ngc544	1.420008	-38.094528
ngc545	1.433089	-1.340222
ngc546	1.420225	-38.069083
ngc547	1.433508	-1.345167
ngc548	1.434031	-1.225611
ngc549	1.418633	-38.00775
ngc550	1.445153	2.022361
ngc551	1.461294	37.182917
ngc552	1.436153	33.405861
ngc553	1.436833	33.405
ngc554	1.452667	-22.725
ngc554a	1.452694	-22.724667
ngc554b	1.452656	-22.725722
ngc555	1.453281	-22.762167
ngc556	1.453503	-22.69775
ngc558	1.454492	-1.970889
ngc559	1.492547	63.301444
ngc561	1.471878	34.308639
ngc562	1.474794	48.387083
ngc564	1.463392	-1.879528
ngc565	1.469494	-1.306028
ngc566	1.484156	32.33225
ngc567	1.450667	-10.26525
ngc569	1.485322	11.131472
ngc570	1.482956	-0.949
ngc571	1.498883	32.501333
ngc572	1.476783	-39.307306
ngc573	1.513708	41.257306
ngc574	1.484189	-35.598917
ngc576	1.482686	-51.598667
ngc577,ngc580	1.511308	-1.994361
ngc578	1.508081	-22.667361
ngc579	1.529581	33.615556
m103,ngc581	1.556058	60.658
ngc582	1.532792	33.476528
ngc583	1.495597	-18.339417
ngc585	1.528372	-0.933306
ngc586	1.526903	-6.89375
ngc587	1.542592	35.358583
ngc588	1.546094	30.647528
ngc589	1.544428	-12.042694
ngc590	1.561367	44.928694
ngc591	1.558686	35.66825
ngc592	1.553247	30.644944
ngc593	1.5391	-12.354444
ngc594	1.549142	-16.536
ngc595	1.559397	30.691556
ngc596	1.5478	-7.031833
ngc597	1.537458	-33.497083
m33,ngc598,triangulumgalaxy,triangulumpinwheel	1.564136	30.660222
ngc599	1.548272	-12.19125
ngc600	1.551472	-7.311417
ngc601	1.551828	-12.20875
ngc602	1.490656	-73.5605
ngc603	1.578861	30.231972
ngc604	1.575886	30.784889
ngc605	1.583986	41.248139
ngc606	1.5806	21.418444
ngc607	1.571214	-7.412806
ngc608	1.591178	33.656722
ngc609	1.606594	64.536583
ngc610	1.571667	-20.144222
ngc611	1.571669	-20.127556
ngc612	1.566039	-36.49325
ngc613	1.571714	-29.418361
ngc614,ngc618,ngc627	1.59785	33.681889
ngc615	1.584911	-7.340306
ngc616	1.601167	33.770222
ngc617	1.567372	-9.774139
ngc619	1.581053	-36.489389
ngc620	1.616578	42.323333
ngc621	1.613628	35.512194
ngc622	1.600044	0.663528
ngc623	1.585108	-36.490222
ngc624	1.597525	-10.002972
ngc625	1.584619	-41.436194
ngc626	1.586689	-39.146056
m74,ngc628	1.611597	15.783667
ngc629	1.649594	72.867083
ngc630	1.593467	-39.357833
ngc631	1.613072	5.835361
ngc632	1.621536	5.877639
ngc633	1.6065	-37.321556
ngc634	1.638517	35.364833
ngc635	1.638294	-22.928917
ngc636	1.651814	-7.512611
ngc637	1.717531	64.036556
ngc638	1.660514	7.237333
ngc639	1.649736	-29.925333
ngc640	1.656911	-9.401167
ngc641	1.644231	-42.527528
ngc642	1.651758	-29.914889
ngc643	1.583731	-75.556861
ngc643a	1.510692	-76.0545
ngc643b	1.653536	-75.011111
ngc643c	1.696981	-75.268111
ngc644	1.648044	-42.585278
ngc645	1.669083	5.726694
ngc646	1.62375	-64.896389
ngc647	1.665608	-9.242389
ngc649	1.668736	-9.272111
barbellnebula,corknebula,littledumbbellnebula,m76,ngc650,ngc651	1.705469	51.575472
ngc652	1.678689	7.982917
ngc653	1.70715	35.638333
ngc654	1.733175	61.882722
ngc655	1.698647	-13.08175
ngc656	1.707567	26.143056
ngc657	1.722444	55.836389
ngc658	1.702683	12.601889
ngc659	1.739719	60.669167
ngc660	1.717333	13.645056
ngc661	1.737394	28.705917
ngc662	1.743181	37.695778
ngc663	1.771125	61.218194
ngc664	1.729392	4.222889
ngc665	1.748917	10.423028
ngc666	1.768389	34.374528
ngc667	1.749078	-22.918944
ngc668	1.772964	36.460306
ngc669	1.787819	35.563306
ngc670	1.790236	27.88575
ngc671	1.783103	13.125111
ngc672	1.798478	27.432778
ngc673	1.806233	11.521306
ngc674,ngc697	1.854881	22.357972
ngc675	1.819058	13.059889
ngc676	1.815919	5.907528
ngc677	1.820572	13.055361
ngc678	1.823572	21.997306
ngc679	1.828828	35.785639
ngc680	1.829803	21.970861
ngc681	1.819675	-10.426417
ngc682	1.817944	-14.974833
ngc683	1.829636	11.701306
ngc685	1.795225	-52.761806
ngc686	1.815594	-23.798139
ngc687	1.842567	36.370806
ngc688	1.845606	35.284528
ngc689	1.831047	-27.466611
ngc690	1.796689	-16.722
ngc691	1.844922	21.759917
ngc692	1.811664	-48.6485
ngc693	1.841903	6.145222
ngc694	1.849581	21.9975
ngc695	1.853956	22.582361
ngc696	1.82535	-34.905167
ngc698	1.828806	-34.831083
ngc699	1.845467	-12.035667
ngc700	1.871344	36.036722
ngc701	1.851067	-9.702611
ngc702	1.855222	-4.051944
ngc703	1.877667	36.171417
ngc704	1.877389	36.124167
ngc704a	1.877772	36.120944
ngc704b	1.877139	36.126806
ngc705	1.8782	36.144
ngc706	1.864036	6.296889
ngc707	1.857528	-8.505361
ngc708	1.879578	36.151833
ngc709	1.880728	36.223444
ngc710	1.88165	36.052889
ngc711	1.874378	17.512667
ngc712	1.885678	36.819861
ngc713	1.922647	-9.08375
ngc714	1.891569	36.221306
ngc715	1.886811	-12.872833
ngc717	1.898642	36.229417
ngc718	1.887028	4.195833
ngc720	1.883472	-13.738667
ngc721	1.912628	39.383528
ngc722	1.913042	20.698222
ngc723,ngc724	1.896022	-23.75775
ngc725	1.876525	-16.517806
ngc726	1.925519	-10.799806
ngc727,ngc729	1.89705	-35.856167
ngc728	1.917067	4.222583
ngc730	1.921667	5.636389
ngc731,ngc757	1.915614	-9.010806
ngc732	1.941031	36.802222
ngc733	1.942747	33.055306
ngc734	1.891317	-16.995694
ngc735	1.943883	34.176778
ngc736	1.944686	33.0435
ngc737	1.944667	33.048917
ngc738	1.946025	33.058333
ngc739	1.948525	33.266694
ngc740	1.948575	33.015167
ngc742	1.940047	5.626694
ngc743	1.975358	60.166306
ngc744	1.974978	55.474611
ngc745	1.902406	-56.69075
ngc746	1.964169	44.918583
ngc747	1.958458	-9.462361
ngc748	1.939389	-4.467639
ngc749	1.928089	-29.922333
ngc750	1.959092	33.209278
ngc751	1.959164	33.203083
ngc752	1.959672	37.833389
ngc753	1.961722	35.916111
ngc754	1.905789	-56.761056
ngc755,ngc763	1.939633	-9.061417
ngc756	1.908069	-16.707167
ngc758	1.928372	-3.066472
ngc759	1.963981	36.343111
ngc760	1.963167	33.355389
ngc761	1.963775	33.377139
ngc762	1.949386	-5.402861
ngc764	1.950908	-16.0625
ngc765	1.98	24.892472
ngc766	1.978319	8.346639
ngc767	1.980778	-9.587139
ngc768	1.978036	0.529222
ngc769	1.993306	30.909917
ngc770	1.987122	18.954667
ngc771	2.057386	72.420889
ngc772	1.988772	19.007528
ngc773	1.981111	-11.514639
ngc774	1.992981	14.008194
ngc775	1.975742	-26.293722
ngc776	1.998469	23.644389
ngc777	2.004139	31.429583
ngc778	2.0054	31.313028
ngc779	1.995078	-5.963194
ngc780	2.009772	28.225139
ngc781	2.002489	12.656111
ngc782	1.961217	-57.790167
ngc784	2.021369	28.83725
ngc786	2.023533	15.646528
ngc787	2.013506	-9.002583
ngc788	2.018458	-6.815528
ngc789	2.040558	32.07225
ngc790	2.022667	-5.370972
ngc791	2.02895	8.499944
ngc792	2.037592	15.712194
ngc793	2.048483	31.980722
ngc795	1.997044	-55.824167
ngc796	1.945486	-74.22
ngc797	2.057306	38.114444
ngc798	2.055444	32.077528
ngc799	2.036761	-0.100639
ngc800	2.036625	-0.130444
ngc801	2.062453	38.258722
ngc802	1.985	-67.870139
ngc803	2.062417	16.030972
ngc805	2.074881	28.812333
ngc806	2.058653	-9.933361
ngc807	2.082128	28.987444
ngc808	2.065722	-23.311611
ngc809	2.071936	-8.735306
ngc810	2.091361	13.251389
ngc811	2.076344	-10.108472
ngc812	2.114306	44.572917
ngc813	2.026686	-68.439194
ngc814	2.177119	-15.773583
ngc815	2.177611	-15.812778
ngc816	2.135792	29.255833
ngc817	2.126031	17.202639
ngc818	2.1457	38.777194
ngc819	2.142881	29.234028
ngc820	2.140272	14.349556
ngc821	2.139206	10.994917
ngc822	2.110872	-41.15675
ngc824	2.114794	-36.453167
ngc825	2.142322	6.323722
ngc826	2.156958	30.739694
ngc827	2.148961	7.971472
ngc828	2.169325	39.190361
ngc829	2.145106	-7.790528
ngc830	2.149633	-7.766806
ngc831	2.159611	6.096333
ngc832	2.183564	35.54125
ngc833	2.155789	-10.133083
ngc834	2.183692	37.666278
ngc835	2.156833	-10.135917
ngc836	2.173578	-22.054861
ngc837	2.171181	-22.4315
ngc838	2.160703	-10.146694
ngc839	2.161925	-10.184083
ngc840	2.171169	7.845306
ngc841	2.188156	37.497167
ngc842	2.164108	-7.762472
ngc843	2.185586	32.097417
ngc844	2.170625	6.049806
ngc845	2.205497	37.477333
ngc846,ngc847	2.203422	44.568389
ngc848	2.171567	-10.321444
ngc849	2.169775	-22.323
ngc850	2.187114	-1.485583
ngc851	2.186692	3.779694
ngc852	2.148739	-56.737056
ngc853	2.194775	-9.306
ngc854	2.191875	-35.835111
ngc855	2.234303	27.877333
ngc856,ngc859	2.227322	-0.717278
ngc857	2.210269	-31.944611
ngc858	2.208381	-22.471528
ngc860	2.250042	30.778806
ngc861	2.264206	35.913583
ngc862	2.2175	-42.033528
ngc863,ngc866,ngc885	2.242656	-0.766694
ngc864	2.257678	6.002611
ngc865	2.270864	28.599722
ngc867,ngc875	2.284661	1.244194
ngc868	2.266244	-0.713639
hperseicluster,ngc869	2.316267	57.11725
ngc870	2.285894	14.523111
ngc871	2.286314	14.547833
ngc872	2.257008	-17.781056
ngc873	2.275656	-11.348556
ngc874	2.266986	-23.301722
ngc876	2.298142	14.521278
ngc877	2.2999	14.544056
ngc878	2.298406	-23.384056
ngc879	2.280889	-8.964028
ngc880	2.30755	-4.20575
ngc881	2.312575	-6.639083
ngc882	2.327753	15.81425
ngc883	2.318106	-6.790917
chiperseicluster,ngc884	2.375583	57.144111
ngc886	2.386603	63.77875
ngc887	2.325725	-16.069722
ngc888	2.290861	-59.861056
ngc889	2.318592	-41.749333
ngc890	2.366947	33.266056
ngc891	2.375947	42.349139
ngc892	2.347783	-23.113639
ngc893	2.332939	-41.403139
ngc894	2.359603	-5.510222
ngc895	2.360131	-5.521389
ngc896	2.424394	62.019361
ngc897	2.351769	-33.720667
ngc898	2.388992	41.951417
ngc899	2.364761	-20.82325
ngc900	2.392272	26.511528
ngc901	2.392803	26.557056
ngc902	2.372711	-16.679056
ngc903	2.400244	27.356278
ngc904	2.401547	27.342389
ngc905	2.378769	-8.719028
ngc906	2.421183	42.089889
ngc907	2.383864	-20.712056
ngc908	2.384603	-21.233861
ngc909	2.422997	42.035667
ngc910	2.424106	41.824278
ngc911	2.428444	41.956278
ngc912	2.428536	41.777444
ngc913	2.429067	41.799417
ngc914	2.434772	42.144083
ngc915	2.429328	27.221
ngc916	2.4299	27.242528
ngc917	2.435469	31.912333
ngc918	2.430789	18.49625
ngc919	2.437964	27.212111
ngc920	2.464383	45.947056
ngc921	2.442617	-15.847528
ngc922	2.417894	-24.788167
ngc923	2.459622	41.977611
ngc924	2.446342	20.4975
ngc925	2.454689	33.579167
ngc926	2.435197	-0.331944
ngc927	2.443697	12.155333
ngc928	2.461394	27.221194
ngc929	2.455061	-12.086917
ngc930	2.464289	20.341778
ngc931	2.470689	31.311667
ngc932	2.465192	20.332472
ngc933	2.488192	45.911306
ngc934	2.459147	-0.244556
ngc935	2.469764	19.599111
ngc936	2.460406	-1.156278
ngc937	2.491133	42.249972
ngc938	2.475975	20.283694
ngc939	2.439256	-44.446167
ngc940,ngc952	2.490972	31.640917
ngc941	2.474403	-1.151528
ngc942	2.486181	-10.836139
ngc943	2.486022	-10.828056
ngc945	2.477022	-10.538972
ngc946	2.510675	42.232611
ngc947	2.475867	-19.042111
ngc948	2.479297	-10.513889
ngc949	2.513514	37.136778
ngc950	2.486603	-11.024694
ngc951	2.482467	-22.349444
ngc953	2.519383	29.58875
ngc954	2.481008	-41.402667
ngc955	2.509208	-1.108417
ngc956	2.541917	44.593472
ngc957	2.555286	57.569694
ngc958	2.511897	-2.939
ngc959	2.539983	35.494639
ngc960	2.528156	-9.300444
ngc962	2.544397	28.069944
ngc965	2.540306	-18.639722
ngc966	2.529767	-19.881694
ngc967	2.536864	-17.216861
ngc968	2.568392	34.479889
ngc969	2.568944	32.946944
ngc970	2.569806	32.976111
ngc971	2.571125	32.987111
ngc972	2.570383	29.311278
ngc973	2.572253	32.505611
ngc974	2.573833	32.9545
ngc975	2.556319	9.601694
ngc976	2.566672	20.976778
ngc977	2.550953	-10.759972
ngc978	2.579889	32.843611
ngc978a	2.579714	32.846194
ngc978b	2.580028	32.841389
ngc979	2.527442	-44.524306
ngc980	2.588489	40.9265
ngc981	2.549969	-10.973944
ngc982	2.590242	40.869722
ngc1002,ngc983	2.648789	34.622278
ngc984	2.578639	23.413
ngc985	2.577158	-8.787611
ngc986	2.559542	-39.045056
ngc986a	2.544847	-39.296222
ngc987	2.613781	33.32725
ngc988	2.591042	-9.356194
ngc989	2.562792	-16.511167
ngc990	2.605058	11.642083
ngc991	2.592411	-7.154444
ngc992	2.623747	21.100833
ngc993,ngc994	2.612794	2.050417
ngc995	2.642233	41.52925
ngc996	2.644408	41.647528
ngc997	2.620694	7.307778
ngc998	2.62125	7.335806
ngc999	2.646517	41.6705
ngc1000	2.64715	41.459694
ngc1001	2.653514	41.671722
ngc1003	2.654692	40.872306
ngc1004	2.628272	1.975306
ngc1005	2.658111	41.488972
ngc1006,ngc1010	2.62635	-11.025
ngc1007	2.631183	2.156028
ngc1008	2.632025	2.079639
ngc1009	2.638631	2.310028
ngc1011	2.627469	-11.005556
ngc1012	2.654142	30.151389
ngc1013	2.630686	-11.50725
ngc1014	2.633569	-9.573389
ngc1015	2.636544	-1.318694
ngc1016	2.638767	2.11925
ngc1017	2.630511	-11.010278
ngc1018	2.636211	-9.543917
ngc1019	2.640947	1.907722
ngc1020	2.64565	2.231278
ngc1021	2.646672	2.217417
ngc1022	2.642419	-6.677417
ngc1023	2.673336	39.063278
ngc1023a	2.677139	39.0575
ngc1024	2.653322	10.846833
ngc1025	2.605536	-54.864167
ngc1026	2.655339	6.544
ngc1028	2.660319	10.843667
ngc1029	2.66015	10.793333
ngc1030	2.664056	18.024278
ngc1031	2.610767	-54.859778
ngc1032	2.656567	1.093778
ngc1033	2.671144	-8.776944
ngc1034	2.637228	-15.809083
ngc1035	2.658081	-8.132944
ngc1037	2.666217	-1.734056
ngc1038	2.668422	1.508778
m34,ngc1039	2.702056	42.746139
ngc1040,ngc1053	2.720122	41.500611
ngc1041	2.673672	-5.440444
ngc1042	2.673325	-8.433556
ngc1043	2.679603	1.343139
ngc1044	2.685167	8.737222
ngc1045	2.674756	-11.277556
ngc1046	2.686903	8.719389
ngc1047	2.675789	-8.147667
ngc1048	2.677208	-8.533361
ngc1048a	2.676583	-8.547222
fornaxdwarfcluster3,ngc1049	2.663372	-34.25825
ngc1050	2.709886	34.7635
ngc1052	2.684667	-8.255778
ngc1054	2.704372	18.217194
ngc1055	2.695897	0.443167
ngc1056	2.713417	28.574194
ngc1057	2.717472	32.491194
ngc1058	2.725	37.341333
ngc1059	2.709889	17.99675
ngc1060	2.720847	32.424972
ngc1061	2.721044	32.466722
ngc1062	2.723339	32.462139
ngc1063	2.702794	-5.568556
ngc1064	2.706536	-9.362278
ngc1065	2.701742	-15.091556
ngc1066	2.730539	32.475
ngc1067	2.7307	32.511889
m77,ngc1068	2.711308	-0.013278
ngc1069	2.716617	-8.2895
ngc1070	2.722853	4.968417
ngc1071	2.718847	-8.773889
ngc1073	2.727922	1.376111
ngc1074	2.7267	-16.297083
ngc1075	2.725986	-16.201111
ngc1076	2.724792	-14.754306
ngc1077	2.767139	40.091667
ngc1077a	2.767472	40.093333
ngc1077b	2.766833	40.090278
ngc1078	2.735567	-9.452389
ngc1079	2.728983	-29.003361
ngc1080	2.752761	-4.710778
ngc1081	2.751533	-15.587806
ngc1082	2.761458	-8.180528
ngc1083	2.761278	-15.357778
ngc1084	2.766642	-7.578472
ngc1085	2.773694	3.607278
ngc1086	2.798992	41.246472
ngc1087	2.773656	-0.498639
ngc1088	2.784556	16.201111
ngc1089	2.769472	-15.073194
ngc1090	2.776094	-0.247167
ngc1091	2.756231	-17.533167
ngc1092	2.758214	-17.542278
ngc1093	2.804486	34.419778
ngc1094	2.791064	-0.285111
ngc1095	2.79385	4.637639
ngc1096	2.730358	-59.913417
ngc1097	2.771958	-30.274889
ngc1097a	2.769417	-30.228056
ngc1098	2.748242	-17.659139
ngc1099	2.755006	-17.708361
ngc1100	2.760019	-17.688944
ngc1101	2.804119	4.578028
ngc1102	2.786917	-22.208833
ngc1103	2.801667	-13.959222
ngc1104	2.810747	-0.271528
ngc1106	2.844586	41.6715
ngc1107	2.822114	8.092639
ngc1108	2.810706	-7.951111
ngc1110	2.819325	-7.837556
ngc1113	2.834736	13.327417
ngc1114	2.818667	-16.993361
ngc1115	2.840383	13.266222
ngc1116	2.843247	13.335056
ngc1117	2.853642	13.185306
ngc1118	2.832964	-12.163722
ngc1119	2.804744	-17.987611
ngc1121	2.844219	-1.734056
ngc1122,ngc1123	2.880889	42.205028
ngc1124	2.859978	-25.701833
ngc1125	2.861186	-16.651028
ngc1126	2.871842	-1.296
ngc1127	2.881067	13.256417
ngc1128	2.961547	6.024667
ngc1129	2.907606	41.579583
ngc1130	2.906772	41.605611
ngc1131	2.909439	41.559028
ngc1132	2.881086	-1.274694
ngc1133	2.878386	-8.804389
ngc1134	2.894817	13.014139
ngc1135	2.84645	-54.929583
ngc1136	2.84825	-54.975917
ngc1137	2.900758	2.962083
ngc1138	2.943456	43.047361
ngc1139	2.879669	-14.529333
ngc1140	2.909328	-10.02775
ngc1141,ngc1143	2.919364	-0.177861
ngc1142,ngc1144	2.920056	-0.183556
ngc1145	2.909308	-18.635083
ngc1146	2.960372	46.426944
ngc1147	2.919247	-9.119639
ngc1148	2.951214	-7.685639
ngc1149	2.956631	-0.309417
ngc1150	2.950386	-15.048417
ngc1151	2.951286	-15.013028
ngc1152	2.959342	-7.758833
ngc1153	2.969522	3.361917
ngc1154	2.968797	-10.363306
ngc1155	2.970303	-10.350583
ngc1156	2.995083	25.237833
ngc1157	2.968522	-15.118528
ngc1158	2.953183	-14.395528
ngc1159	3.012922	43.162556
ngc1160	3.020347	44.955417
ngc1161	3.020592	44.897333
ngc1162	2.982222	-12.398583
ngc1163	3.006136	-17.152528
ngc1164	3.033292	42.584944
ngc1165	2.979914	-32.099194
ngc1166	3.009722	11.842778
ngc1167	3.028436	35.20575
ngc1168	3.013061	11.772306
ngc1169	3.059653	46.386361
ngc1170	3.040803	27.072667
ngc1171	3.066386	43.398306
ngc1172	3.026681	-14.836583
ngc1173	3.066031	42.383722
ngc1174,ngc1186	3.091906	42.8355
ngc1175	3.075653	42.339306
ngc1176	3.076356	42.393444
ngc1178	3.07745	42.313472
ngc1179	3.044022	-18.897778
ngc1180	3.030844	-15.029833
ngc1181	3.028544	-15.052333
ngc1182,ngc1205	3.0579	-9.670333
ngc1183	3.079489	42.368944
ngc1184	3.279175	80.793333
ngc1185	3.049856	-9.132139
ngc1187	3.043775	-22.867167
ngc1188	3.062047	-15.484583
ngc1189	3.056797	-15.623472
ngc1190	3.057258	-15.661889
ngc1191	3.058581	-15.685306
ngc1192	3.059619	-15.678833
ngc1193	3.098797	44.383111
ngc1194	3.063642	-1.10375
ngc1195	3.059114	-12.039778
ngc1196	3.059778	-12.076306
ngc1197	3.103947	44.061194
ngc1199	3.060669	-15.613194
ngc1200	3.065133	-11.991806
ngc1201	3.068883	-26.069639
ngc1202	3.084036	-6.491611
ngc1203	3.087278	-14.378889
ngc1203a	3.08725	-14.381111
ngc1203b	3.087306	-14.377778
ngc1204	3.077756	-12.341389
ngc1206	3.102706	-8.833167
ngc1207	3.137636	38.382167
ngc1208	3.103308	-9.541417
ngc1209	3.100839	-15.61125
ngc1210	3.1126	-25.716444
ngc1211	3.114561	-0.794472
ngc1214	3.115561	-9.544167
ngc1215	3.119294	-9.592667
ngc1216	3.121817	-9.612806
ngc1217	3.101672	-39.036389
ngc1218	3.140617	4.110917
ngc1219	3.141103	2.108583
ngc1220	3.194631	53.348167
ngc1221	3.137647	-4.259472
ngc1222	3.149094	-2.955139
ngc1223	3.138869	-4.138389
ngc1224	3.187097	41.363694
ngc1225	3.14645	-4.101556
ngc1226	3.184819	35.386833
ngc1227	3.185481	35.324861
ngc1228	3.136594	-22.922861
ngc1229	3.136331	-22.960806
ngc1230	3.137889	-22.984
ngc1231	3.108139	-15.569083
ngc1232	3.162642	-20.579306
ngc1232a	3.167194	-20.600556
ngc1233,ngc1235	3.209197	39.318917
ngc1234	3.160858	-7.846194
ngc1236	3.191108	10.808278
ngc1237	3.169158	-8.692333
ngc1238	3.181308	-10.748056
ngc1239	3.181589	-2.553139
ngc1240	3.224078	30.507167
ngc1241	3.1874	-8.922139
ngc1242	3.1887	-8.902417
ngc1243	3.190406	-8.945278
ngc1244	3.108636	-66.775611
ngc1245	3.24485	47.238694
ngc1246	3.117247	-66.938639
ngc1247	3.203978	-10.481111
ngc1248	3.213489	-5.224694
ngc1249	3.167008	-53.33575
ngc1250	3.255861	41.355417
ngc1251	3.235864	1.456528
ngc1252	3.178972	-57.758611
ngc1253	3.235847	-2.822944
ngc1253a	3.239806	-2.800833
ngc1254	3.240014	2.677361
ngc1255	3.225567	-25.725167
ngc1256	3.232853	-21.986417
ngc1257	3.283208	41.529056
ngc1258	3.234853	-21.774278
ngc1259	3.288133	41.3855
ngc1260	3.2909	41.405222
ngc1261	3.204261	-55.216806
ngc1262	3.259328	-15.879306
ngc1263	3.260989	-15.098306
ngc1264	3.299881	41.520278
ngc1265	3.30435	41.85775
ngc1266	3.266875	-2.427361
ngc1267	3.312478	41.467722
ngc1268	3.312544	41.488694
ngc1269,ngc1291	3.288497	-41.108056
ngc1270	3.316153	41.47
ngc1271	3.3198	41.35325
ngc1272	3.322581	41.490639
ngc1273	3.324094	41.540528
ngc1274	3.327931	41.548639
ngc1275,perseusa	3.330044	41.511694
ngc1276	3.330892	41.641972
ngc1277	3.330969	41.573528
ngc1279	3.333075	41.479528
ngc1280	3.299186	-0.169083
ngc1281	3.335031	41.630028
ngc1282	3.3367	41.367
ngc1283	3.337644	41.398667
ngc1284	3.295975	-10.289083
ngc1285	3.298175	-7.297806
ngc1286	3.296814	-7.616861
ngc1287	3.309297	-2.730833
ngc1288	3.286997	-32.575889
ngc1290	3.323658	-13.989611
ngc1292	3.304136	-27.610333
ngc1293	3.360128	41.392833
ngc1294	3.3611	41.360556
ngc1295	3.33425	-13.99825
ngc1296	3.313808	-13.062444
ngc1297	3.320617	-19.1
ngc1298	3.336967	-2.114111
ngc1299	3.336022	-6.262
ngc1300	3.328078	-19.411361
ngc1301	3.343147	-18.715333
ngc1302	3.330883	-26.060444
ngc1303	3.344664	-7.394417
ngc1304,ngc1307	3.35355	-4.584083
ngc1305	3.356381	-2.316833
ngc1306	3.350831	-25.512556
ngc1308	3.374594	-2.757139
ngc1309	3.368489	-15.400056
ngc1310	3.350953	-37.101694
ngc1311	3.335267	-52.185528
ngc1312	3.394925	1.184667
ngc1313	3.304458	-66.49825
ngc1313a	3.334917	-66.701111
ngc1314	3.3781	-4.186556
ngc1315	3.385164	-21.375167
fornaxa,ngc1316	3.378256	-37.208222
ngc1316a	3.393861	-36.903889
ngc1316b	3.394333	-36.908333
ngc1316c	3.416222	-37.009444
fornaxb,ngc1317,ngc1318	3.378969	-37.103694
ngc1319	3.399017	-21.527722
ngc1320	3.413528	-3.042278
ngc1321	3.413492	-3.015583
ngc1322	3.415197	-2.919222
ngc1323	3.415578	-2.822083
ngc1324	3.417133	-5.745806
ngc1325	3.407103	-21.544028
ngc1325a	3.413472	-21.336111
ngc1326	3.399	-36.464667
ngc1326a	3.419028	-36.363889
ngc1326b	3.422306	-36.385
ngc1327	3.423086	-25.680278
ngc1328	3.427528	-4.124944
ngc1329	3.434053	-17.5915
ngc1330	3.484575	41.67525
ngc1332	3.438125	-21.335222
lbn741,ngc1333	3.482	31.37
ngc1334	3.500511	41.832028
ngc1335	3.505414	41.57275
ngc1336	3.442275	-35.713556
ngc1337	3.468322	-8.388611
ngc1338	3.481819	-12.153361
ngc1339	3.468494	-32.286111
ngc1340,ngc1344	3.472131	-31.068167
ngc1341	3.466228	-37.15
ngc1342	3.527811	37.379389
ngc1343	3.630472	72.571333
ngc1345	3.492136	-17.778389
ngc1346	3.503686	-5.543306
ngc1347	3.494861	-22.285
ngc1348	3.569025	51.420528
ngc1349	3.524306	4.380833
ngc1350	3.518922	-33.628639
ngc1351	3.509717	-34.853944
ngc1351a	3.480194	-35.178056
ngc1352	3.525828	-19.278444
ngc1353	3.534172	-20.819167
ngc1354	3.541492	-15.221139
ngc1355	3.556528	-4.998694
ngc1356	3.511331	-50.309611
ngc1357	3.554744	-13.664139
ngc1358	3.561019	-5.089389
ngc1359	3.563253	-19.492056
ngc1360	3.554069	-25.871722
ngc1361	3.571594	-6.265
ngc1362	3.564744	-20.282639
ngc1363	3.580436	-9.842472
ngc1364	3.58305	-9.838639
ngc1365	3.560103	-36.140389
ngc1366	3.564911	-31.194111
ngc1367,ngc1371	3.583706	-24.933222
ngc1368	3.583028	-15.655917
ngc1369	3.612569	-36.256222
ngc1370	3.587381	-20.373667
ngc1372	3.616594	-15.881472
ngc1373	3.583114	-35.171111
ngc1374	3.587942	-35.22625
ngc1375	3.588006	-35.265667
ngc1376	3.618311	-5.04275
ngc1377	3.610856	-20.90225
ngc1378	3.5995	-35.211167
ngc1379	3.601097	-35.441194
ngc1380	3.607664	-34.976222
ngc1380a	3.613194	-34.739722
ngc1380b,ngc1382	3.619156	-35.195028
ngc1381	3.6088	-35.295194
ngc1383	3.627567	-18.339472
ngc1384	3.653775	15.819556
ngc1385	3.624681	-24.500306
ngc1386	3.612828	-35.999417
ngc1387	3.61585	-35.506639
ngc1388	3.636669	-15.899417
ngc1389	3.619939	-35.745583
ngc1390	3.631158	-19.008361
ngc1391	3.648044	-18.354111
ngc1392	3.629725	-36.147417
ngc1393	3.64405	-18.427972
ngc1394	3.651922	-18.292278
ngc1395	3.641597	-23.027528
ngc1396	3.63515	-35.440111
ngc1397	3.663097	-4.670111
ngc1398	3.647814	-26.337833
ngc1399	3.641397	-35.450667
ngc1400	3.658567	-18.688083
ngc1401	3.656069	-22.724694
ngc1402	3.658492	-18.526944
ngc1403	3.653011	-22.38875
ngc1404	3.647756	-35.594389
ngc1405	3.671925	-15.530194
ngc1406	3.656472	-31.321417
ngc1407	3.669961	-18.580111
ngc1408	3.6548	-35.500833
ngc1409	3.686231	-1.302556
ngc1410	3.686319	-1.298778
ngc1413	3.669875	-15.610778
ngc1414	3.682511	-21.713139
ngc1416	3.684136	-22.719111
ngc1417	3.699283	-4.704861
ngc1418	3.704489	-4.73075
ngc1419	3.678364	-37.510833
ngc1420	3.711067	-5.852556
ngc1421	3.708133	-13.488028
ngc1422	3.691964	-21.681528
ngc1423	3.711139	-6.381833
ngc1424	3.720567	-4.730083
ngc1425	3.703186	-29.893333
ngc1426	3.713642	-22.108361
ngc1427	3.705394	-35.392556
ngc1427a	3.66925	-35.624444
ngc1428	3.706314	-35.154
ngc1429	3.734478	-4.718111
ngc1430	3.723672	-18.225083
ngc1431	3.744667	2.834944
lbn771,maianebula,ngc1432	3.763775	24.367861
ngc1433	3.700431	-47.222083
ngc1434	3.770242	-9.682611
meropenebula,ngc1435	3.769469	23.764972
ngc1436,ngc1437	3.726967	-35.853028
ngc1437b	3.765222	-36.356944
ngc1438	3.754786	-23.002472
ngc1439	3.747208	-21.920556
ngc1440,ngc1442	3.750808	-18.266028
ngc1441	3.761978	-4.091583
ngc1443	3.764733	-4.052722
ngc1444	3.824689	52.655333
ngc1445	3.74895	-9.855861
ngc1446	3.765961	-4.112167
ngc1447	3.763097	-9.018694
ngc1448,ngc1457	3.7422	-44.644833
ngc1449	3.767519	-4.138111
ngc1450	3.760178	-9.234861
ngc1451	3.768656	-4.069194
ngc1452,ngc1455	3.756197	-18.633639
ngc1453	3.774236	-3.968778
ngc1454	3.766483	-20.652306
ngc1456	3.802292	22.558611
ngc1458	3.782864	-18.241139
ngc1459	3.782761	-25.52175
ngc1460	3.770483	-36.696333
ngc1461	3.807539	-16.392889
ngc1462	3.839842	6.973056
ngc1463	3.77095	-59.810139
ngc1464,ngc1471	3.856811	-15.40225
ngc1465	3.892197	32.492806
ngc1466	3.742597	-71.671583
ngc1467	3.864667	-8.838194
ngc1468	3.870161	-6.348944
ngc1469	4.007714	68.577722
ngc1470	3.8694	-8.999361
ngc1472	3.896486	-8.568472
ngc1473	3.790639	-68.220583
ngc1475	3.897175	-8.1375
ngc1476	3.869108	-44.532472
ngc1477	3.9008	-8.574972
ngc1478	3.902039	-8.555417
ngc1479	3.905678	-10.208611
ngc1480	3.908994	-10.258833
ngc1481	3.908044	-20.427167
ngc1482	3.910822	-20.502667
ngc1483	3.8799	-47.477528
ngc1484	3.905592	-36.968889
ngc1485	4.084428	70.996528
ngc1486	3.938528	-21.821139
ngc1487	3.929472	-42.368056
ngc1488	4.001203	18.567306
ngc1489	3.960583	-19.216639
ngc1490	3.892839	-66.018056
lbn704,ngc1491	4.053767	51.316083
ngc1492	3.970314	-35.446361
ngc1493	3.957619	-46.210694
ngc1494	3.961917	-48.908083
ngc1495	3.972728	-44.46625
ngc1496	4.075525	52.661389
ngc1497	4.035228	23.132917
ngc1498	4.005361	-12.019722
californianebula,lbn756,ngc1499	4.054006	36.367472
ngc1500	3.970547	-52.328167
ngc1501	4.116492	60.920694
ngc1502	4.130361	62.331528
ngc1503	3.942567	-66.040667
ngc1504	4.041583	-9.335389
ngc1505	4.043444	-9.322417
ngc1506	4.005992	-52.573722
ngc1507	4.074225	-2.188583
ngc1508	4.096567	25.408472
ngc1510	4.059067	-43.400111
ngc1511	3.993606	-67.63425
ngc1511a	4.005167	-67.806944
ngc1511b	4.015194	-67.611944
ngc1512	4.065078	-43.348861
ngc1513	4.165194	49.517278
ngc1514	4.154708	30.775917
ngc1515	4.067422	-54.100056
ngc1515a	4.063833	-54.113056
ngc1516	4.135472	-8.831389
ngc1516a,ngc1524	4.135389	-8.829167
ngc1516b,ngc1525	4.135642	-8.835722
ngc1517	4.153314	8.648806
ngc1518	4.113811	-21.172639
ngc1519	4.135444	-17.192889
ngc1520	3.958603	-76.833944
ngc1521	4.138592	-21.051972
ngc1522	4.1022	-52.668417
ngc1523	4.103061	-54.088306
ngc1526	4.08675	-65.839806
ngc1527	4.140039	-47.897028
ngc1528	4.255242	51.211472
ngc1529	4.122189	-62.899306
ngc1530	4.390861	75.295583
ngc1531	4.199811	-32.850806
ngc1532	4.201203	-32.874222
ngc1533	4.1644	-56.118444
ngc1534	4.146131	-62.797583
ngc1535	4.237714	-12.739389
ngc1536	4.183294	-56.480444
ngc1537	4.227975	-31.645417
ngc1539	4.317211	26.8275
ngc1540	4.252961	-28.488472
ngc1540a	4.252781	-28.482083
ngc1541	4.283397	0.835194
ngc1542	4.287272	4.781639
ngc1543	4.212014	-57.737972
ngc1544	5.043375	86.222333
ngc1545	4.348961	50.255333
ngc1546	4.243483	-56.060806
ngc1547	4.286781	-17.857472
ngc1548	4.355306	36.916333
ngc1549	4.262536	-55.59225
ngc1550,ngc1551	4.327203	2.409472
ngc1552	4.338244	-0.692722
ngc1553	4.269575	-55.780139
ngc1554	4.362097	19.520583
hindsnebula,hindsvariablenebula,ngc1555	4.366508	19.535167
ngc1556	4.295786	-50.164444
ngc1557	4.219769	-70.424944
ngc1558	4.337828	-45.031472
ngc1559	4.293269	-62.783667
ngc1560	4.546969	71.883111
ngc1561	4.383633	-15.845667
ngc1562	4.363228	-15.755444
ngc1563	4.381653	-15.732639
ngc1564	4.383597	-15.738861
ngc1565	4.389847	-15.744333
ngc1566	4.33345	-54.937806
ngc1567	4.352431	-48.254778
ngc1568	4.407039	-0.746222
ngc1569	4.513628	64.847944
ngc1570,ngc1571	4.36915	-43.629556
ngc1572	4.378558	-40.600917
ngc1573	4.584442	73.262417
ngc1574	4.366339	-56.97475
ngc1575,ngc1577	4.439042	-10.098444
ngc1576	4.438561	-3.621083
ngc1578	4.396292	-51.599444
lbn767,ngc1579	4.503833	35.269444
ngc1580	4.4718	-5.178778
ngc1581	4.412489	-54.942
ngc1582	4.529664	43.784833
ngc1583	4.472425	-17.595444
ngc1584	4.469517	-17.523361
ngc1585	4.459169	-42.165222
ngc1586	4.510619	-0.304167
ngc1587	4.511094	0.661583
ngc1588	4.512158	0.664722
ngc1589	4.512622	0.863667
ngc1590	4.519506	7.630889
ngc1591	4.491819	-26.713111
ngc1592	4.494481	-27.408528
ngc1595	4.472711	-47.815889
ngc1596	4.460586	-55.027806
ngc1597	4.520406	-11.290417
ngc1598	4.476019	-47.782556
ngc1599	4.527428	-4.588333
ngc1600	4.527761	-5.08625
ngc1601	4.528258	-5.060361
ngc1602	4.465269	-55.057722
ngc1603	4.530542	-5.094417
ngc1604	4.532936	-5.369944
ngc1605	4.581189	45.271389
ngc1606	4.534261	-5.032444
ngc1607	4.534192	-4.459944
ngc1609	4.545856	-4.372417
ngc1610,ngc1619	4.570519	-4.69975
ngc1611	4.551656	-4.297444
ngc1612	4.553647	-4.172417
ngc1613	4.557036	-4.265417
ngc1614	4.566625	-8.578889
ngc1615	4.600289	19.950333
ngc1616	4.544925	-43.715889
ngc1617	4.527647	-54.602278
ngc1618	4.601833	-3.14875
ngc1620	4.610375	-0.143611
ngc1621,ngc1626	4.606961	-4.987306
ngc1622	4.610178	-3.188833
ngc1623	4.592336	-13.556444
lbn722,ngc1624	4.676806	50.461667
ngc1625	4.618406	-3.3035
ngc1627	4.627222	-4.887472
ngc1628	4.626739	-4.714833
ngc1629	4.493586	-71.838278
ngc1630	4.620967	-18.901528
ngc1631	4.640047	-20.649861
ngc1633	4.669197	7.349444
ngc1634	4.669383	7.338778
ngc1635	4.668856	-0.547528
ngc1636	4.677833	-8.60775
ngc1637	4.691161	-2.857972
ngc1638	4.693475	-1.809028
ngc1639	4.681169	-16.990861
ngc1640	4.704033	-20.434778
ngc1641	4.593033	-65.762889
ngc1642	4.715253	0.618583
ngc1643	4.728875	-5.319444
ngc1644	4.627803	-66.199083
ngc1645	4.735106	-5.465611
ngc1646	4.739889	-8.532778
ngc1647	4.765436	19.095111
ngc1648	4.743	-8.478861
ngc1649,ngc1652	4.639681	-68.672917
ngc1650	4.753197	-15.870028
ngc1651	4.625631	-70.585861
ngc1653	4.763153	-2.392833
ngc1654	4.763458	-2.083889
ngc1655	4.786639	20.923667
ngc1656	4.764831	-5.136722
ngc1657	4.768683	-2.077278
ngc1658	4.733711	-41.463417
ngc1659	4.774986	-4.788778
ngc1660	4.736503	-41.497583
ngc1661	4.785456	-2.054583
ngc1662	4.808042	10.930389
ngc1663	4.823206	13.151056
ngc1664	4.851508	43.676167
ngc1665	4.804742	-5.427611
ngc1666	4.809122	-6.569972
ngc1667,ngc1689	4.810317	-6.319972
ngc1668	4.768314	-44.733361
ngc1669	4.716639	-65.814333
ngc1670	4.828506	-2.7605
ngc1672	4.761806	-59.247194
ngc1673	4.711011	-69.82125
ngc1674,ngc1675	4.873603	23.907667
ngc1676	4.731714	-68.827583
ngc1678	4.859844	-2.623139
ngc1679	4.831844	-31.964667
ngc1680	4.809447	-47.816444
ngc1681	4.863906	-5.803222
ngc1682	4.872164	-3.105861
ngc1683	4.871556	-3.024639
ngc1684	4.875319	-3.106056
ngc1685	4.876175	-2.949333
ngc1686	4.88185	-15.346472
ngc1687	4.855936	-33.939028
ngc1688	4.806608	-59.800333
ngc1690	4.90535	1.640361
ngc1691	4.91065	3.267972
ngc1692	4.923258	-20.571167
ngc1693	4.794103	-69.343639
ngc1694	4.921339	-4.652667
ngc1695	4.795689	-69.37375
ngc1696	4.808325	-68.242861
ngc1697	4.809947	-68.558444
ngc1698	4.818069	-69.115083
ngc1699	4.949897	-4.756861
ngc1700	4.948975	-4.865778
ngc1701	4.930869	-29.883444
ngc1702	4.824356	-69.850778
ngc1703	4.881153	-59.74225
ngc1704	4.832072	-69.756306
ngc1705	4.90375	-53.361056
ngc1706	4.875283	-62.985778
ngc1708	5.056078	52.832083
ngc1709	4.978897	-0.47825
ngc1711	4.843369	-69.985444
ngc1712	4.849564	-69.4075
ngc1713	4.981836	-0.488917
ngc1714	4.869125	-66.923389
ngc1715	4.869578	-66.908694
ngc1716	4.970367	-20.363583
ngc1717	4.975406	-0.574667
ngc1718	4.873719	-67.050667
ngc1719	4.992953	-0.260417
ngc1720	4.989064	-7.858972
ngc1721	4.988167	-11.118722
ngc1722	4.866833	-69.375
ngc1723	4.990525	-10.980694
ngc1724	5.058978	49.491778
ngc1725	4.989692	-11.132306
ngc1726	4.994972	-7.75525
ngc1727	4.870214	-69.338917
ngc1728	4.991036	-11.122944
ngc1729	5.004358	-3.3525
ngc1731	4.892247	-66.925278
ngc1732	4.886275	-68.65
ngc1733	4.901319	-66.682583
ngc1734	4.892636	-68.768778
ngc1735	4.905461	-67.099556
ngc1736	4.883764	-68.053111
ngc1737	4.899919	-69.174556
ngc1738	5.029639	-18.157056
ngc1739	5.029817	-18.166806
ngc1740	5.031889	-3.296333
ngc1741	5.027306	-4.257
ngc1741b	5.026722	-4.261944
ngc1742	5.033147	-3.294972
ngc1743	4.900742	-69.198611
ngc1744	4.999389	-26.022222
ngc1745	4.905728	-69.158889
ngc1746	5.063942	23.767639
ngc1747	4.919717	-67.168889
ngc1749	4.915572	-68.188667
ngc1750	5.066675	23.645778
ngc1751	4.903494	-69.805833
ngc1752	5.035969	-8.240861
ngc1753	5.042317	-3.344333
ngc1754	4.905264	-70.442472
ngc1755	4.920797	-68.204056
ngc1756	4.913842	-69.237639
ngc1757	5.044267	-4.722944
ngc1758	5.0784	23.781639
ngc1759	5.013622	-38.673889
ngc1760	4.945658	-66.527333
ngc1761	4.943814	-66.478861
ngc1762	5.060286	1.573333
ngc1763	4.946997	-66.409083
ngc1764	4.941033	-67.69375
ngc1765	4.973378	-62.028389
ngc1766	4.932667	-70.225056
ngc1767	4.940917	-69.400556
ngc1768	4.950044	-68.249444
ngc1769	4.963158	-66.469083
ngc1770	4.954364	-68.418083
ngc1771	4.982144	-63.298222
ngc1772	4.947997	-69.556056
ngc1773	4.970008	-66.360111
ngc1774	4.968578	-67.242333
ngc1775	4.94855	-70.432
ngc1776	4.9777	-66.429583
ngc1777	4.929906	-74.285361
ngc1778	5.134917	37.022833
ngc1779	5.088353	-9.147139
ngc1780	5.105753	-19.466667
ngc1781,ngc1794	5.131953	-18.189917
ngc1782	4.964192	-69.392194
ngc1783	4.985781	-65.987278
ngc1784	5.090861	-11.871528
ngc1785	4.979156	-68.824861
ngc1786	4.985506	-67.745222
ngc1787	5.029003	-65.823306
lbn916,ngc1788	5.114783	-3.340972
ngc1789	4.964356	-71.901972
ngc1790	5.182283	52.059806
ngc1791	4.985133	-70.16875
ngc1792	5.087347	-37.98075
ngc1793	4.993947	-69.557639
ngc1795	4.996361	-69.801167
ngc1796	5.045153	-61.140056
ngc1796a	5.084167	-61.484444
ngc1796b	5.131917	-61.191111
ngc1797	5.129133	-8.019083
ngc1798	5.194256	47.6955
ngc1799	5.129061	-7.969278
ngc1800	5.107144	-31.954222
ngc1801	5.009586	-69.61375
ngc1802	5.170242	24.125139
ngc1803	5.090717	-49.567944
ngc1804	5.017572	-69.082583
ngc1805	5.039256	-66.11225
ngc1806	5.036769	-67.98575
ngc1807	5.179175	16.51275
ngc1808	5.128428	-37.513056
ngc1809	5.034725	-69.568278
ngc1810	5.056464	-66.381806
ngc1811	5.145206	-29.275972
ngc1812	5.148031	-29.25125
ngc1813	5.044522	-70.317944
ngc1814	5.062906	-67.300667
ngc1815	5.040903	-70.621056
ngc1816	5.064097	-67.26075
ngc1817	5.207297	16.684083
ngc1818	5.070767	-66.4345
ngc1819	5.19615	5.200611
ngc1820	5.067133	-67.265944
ngc1821	5.196139	-15.134639
ngc1822	5.085889	-66.210556
ngc1823	5.056933	-70.3355
ngc1824	5.115611	-59.723972
ngc1825	5.071956	-68.926417
ngc1826	5.092581	-66.22975
ngc1827	5.167944	-36.96025
ngc1828	5.072467	-69.388167
ngc1829	5.083333	-68.05925
ngc1830	5.077297	-69.340167
ngc1831	5.104644	-64.9175
ngc1832	5.200925	-15.687806
ngc1833	5.073475	-70.728056
ngc1834	5.086494	-69.207472
ngc1835	5.085161	-69.403861
ngc1836	5.092894	-68.627889
ngc1837	5.082167	-70.714
ngc1838	5.102189	-68.445194
ngc1839	5.100653	-68.626778
ngc1840	5.088656	-71.762889
ngc1841	4.756486	-83.999056
ngc1842	5.121694	-67.273167
ngc1843	5.235006	-10.627028
ngc1844	5.125189	-67.323417
ngc1845	5.095836	-70.581611
ngc1846	5.126094	-67.461472
ngc1847	5.118933	-68.971444
ngc1848	5.124211	-71.195361
ngc1849	5.159669	-66.315806
ngc1850	5.145758	-68.761667
ngc1851	5.235203	-40.046611
ngc1852	5.156608	-67.77625
ngc1853	5.204589	-57.399028
ngc1854	5.155525	-68.847361
ngc1855	5.154697	-68.845639
ngc1856	5.158158	-69.127583
ngc1857	5.334878	39.343611
ngc1858	5.164428	-68.89125
ngc1859	5.192164	-65.249722
ngc1860	5.177642	-68.75225
ngc1861	5.172817	-70.777111
ngc1862	5.209594	-66.154361
ngc1863	5.194328	-68.726778
ngc1864	5.211278	-67.62125
ngc1865	5.206967	-68.771028
ngc1866	5.227528	-65.465583
ngc1867	5.228406	-66.291944
ngc1868	5.243417	-63.9545
ngc1869	5.232311	-67.379389
ngc1870	5.219417	-69.116944
ngc1871	5.231044	-67.452639
ngc1872	5.219658	-69.311583
ngc1873	5.232131	-67.334361
ngc1874	5.219906	-69.376222
ngc1875	5.362711	6.688861
ngc1876	5.221842	-69.362139
ngc1877	5.227456	-69.383778
ngc1878	5.214142	-70.471694
ngc1879	5.330064	-32.14275
ngc1880	5.223661	-69.379444
ngc1881	5.226992	-69.299167
ngc1882	5.259258	-66.129556
ngc1883	5.431722	46.490139
ngc1884	5.266122	-66.163389
ngc1885	5.251628	-68.977556
ngc1886	5.363375	-23.810139
ngc1887	5.268314	-66.318556
ngc1888	5.376236	-11.499528
ngc1889	5.376472	-11.496944
ngc1890	5.229397	-72.077972
ngc1891	5.362283	-35.789306
ngc1892	5.285847	-64.95975
ngc1893	5.378928	33.412028
ngc1894	5.264242	-69.468528
ngc1895	5.280997	-67.329583
ngc1896	5.4263	29.260222
ngc1897	5.292022	-67.451
ngc1898	5.278439	-69.656222
ngc1899	5.296853	-67.900722
ngc1900	5.319272	-63.023694
ngc1901	5.304211	-68.436306
ngc1902	5.305317	-66.627417
ngc1903	5.289528	-69.335306
m79,ngc1904	5.402942	-24.524222
ngc1905	5.306586	-67.278167
ngc1906	5.413083	-15.943306
ngc1907	5.467931	35.325667
ngc1908	5.431611	-2.528889
ngc1910	5.311964	-69.231917
ngc1911	5.324133	-66.68425
m38,ngc1912	5.478469	35.854917
ngc1913	5.305358	-69.536472
ngc1914	5.294378	-71.255861
ngc1915	5.3284	-66.821528
ngc1916	5.310131	-69.406806
ngc1917	5.317214	-68.998972
ngc1918	5.318608	-69.662444
ngc1919	5.338625	-66.891139
ngc1920	5.342639	-66.778722
ngc1921	5.322986	-69.78775
ngc1922	5.330256	-69.44825
ngc1923	5.359461	-65.486722
ngc1924	5.467203	-5.31075
ngc1925	5.362211	-65.793611
ngc1926	5.343175	-69.525278
ngc1927	5.478606	-8.377333
ngc1928	5.349028	-69.477944
ngc1929	5.360008	-67.912056
ngc1930	5.432444	-46.728472
lbn810,ngc1931	5.523708	34.246556
ngc1932	5.371456	-66.154333
ngc1933	5.374256	-66.152167
ngc1934	5.363303	-67.937167
ngc1937	5.374767	-67.894667
ngc1938	5.356864	-69.939389
ngc1939	5.357392	-69.94975
ngc1940	5.378817	-67.186556
ngc1941	5.385472	-66.378639
ngc1942	5.412372	-63.942111
ngc1943	5.37465	-70.154861
ngc1944	5.365953	-72.494083
ngc1945	5.415267	-66.457472
ngc1946	5.421217	-66.394556
ngc1947	5.446558	-63.760028
ngc1948	5.429511	-66.266806
ngc1949	5.418008	-68.472528
ngc1950	5.409164	-69.902306
ngc1951	5.435228	-66.59725
crabnebula,lbn833,m1,ngc1952	5.575547	22.014472
ngc1953	5.424392	-68.838306
ngc1954	5.546758	-14.062778
ngc1955	5.4361	-67.497389
ngc1956	5.326478	-77.728667
ngc1957	5.548667	-14.133139
ngc1958	5.425144	-69.836778
ngc1959	5.426842	-69.926917
m36,ngc1960	5.604928	34.14075
ngc1962	5.438258	-68.837639
ngc1963	5.538008	-36.398639
ngc1964	5.556044	-21.945778
ngc1965	5.442017	-68.805472
ngc1966	5.446067	-68.819861
ngc1967	5.445364	-69.101528
ngc1968	5.456142	-67.463833
ngc1969	5.442322	-69.841361
ngc1970	5.447964	-68.836667
ngc1971	5.4459	-69.851611
ngc1972	5.446489	-69.838333
ngc1973	5.584661	-4.731778
ngc1974,ngc1991	5.466394	-67.424139
ngc1975	5.5883	-4.685222
greatorionnebula,lbn974,m42,ngc1976,orionnebula	5.587911	-5.389667
ngc1977,therunningmannebula	5.587722	-4.844333
ngc1978	5.479203	-66.235917
ngc1979	5.566975	-23.310083
lbn977,lowersword,ngc1980	5.590553	-5.909889
ngc1981,uppersword	5.585997	-4.425056
m43,mairansnebula,ngc1982	5.59205	-5.267472
ngc1983	5.462292	-68.986056
ngc1984	5.461364	-69.134333
ngc1985	5.629947	31.988833
ngc1986	5.460578	-69.973639
ngc1987	5.454764	-70.737361
ngc1988	5.624025	21.21825
ngc1989	5.573172	-30.801056
alnilam,ngc1990	5.603561	-1.201917
ngc1992	5.575492	-30.897
ngc1993	5.590436	-17.815306
ngc1994	5.472714	-69.141833
ngc1995	5.550928	-48.675139
ngc1996	5.638578	25.823167
ngc1997	5.509639	-63.199528
ngc1998	5.554378	-48.695611
lbn979,ngc1999	5.607042	-6.715861
ngc2000	5.458122	-71.879389
ngc2001	5.483906	-68.769278
ngc2002	5.50575	-66.885
ngc2003	5.515333	-66.466556
ngc2004	5.511875	-67.286444
ngc2005	5.503014	-69.752417
ngc2006	5.5225	-66.965278
ngc2007	5.583103	-50.921694
ngc2008	5.584392	-50.966778
ngc2009	5.516433	-69.181667
ngc2010	5.509703	-70.819667
ngc2011	5.538947	-67.523139
ngc2012	5.376486	-79.851806
ngc2013	5.733797	55.793583
ngc2014	5.538853	-67.689833
ngc2015	5.535136	-69.243028
ngc2016	5.52745	-69.945861
ngc2017	5.654531	-17.8485
ngc2018	5.523581	-71.069056
ngc2019	5.532406	-70.159583
ngc2020	5.553497	-67.715889
ngc2021	5.558519	-67.452889
ngc2022	5.701725	9.086528
lbn954,ngc2023	5.693997	-2.259028
ngc2024	5.695158	-1.856278
ngc2025	5.542678	-71.7155
ngc2026	5.719486	20.138889
ngc2027	5.583253	-66.916306
ngc2028	5.563492	-69.951806
ngc2029	5.594628	-66.035
ngc2030	5.583261	-67.556361
ngc2031	5.561617	-70.986778
ngc2032	5.589061	-67.568444
ngc2033	5.575194	-69.780139
ngc2034	5.592436	-66.903639
ngc2035	5.592	-67.584167
ngc2036	5.575386	-70.064361
ngc2037	5.583508	-69.731583
ngc2038	5.578408	-70.562944
ngc2039	5.733586	8.691056
ngc2040	5.601647	-67.568556
ngc2041	5.607792	-66.989778
ngc2042	5.602661	-68.923444
ngc2043	5.599217	-70.074417
ngc2044	5.601717	-69.198667
ngc2045	5.750361	12.888361
ngc2046	5.593758	-70.240694
ngc2047	5.598053	-70.192667
ngc2048	5.598775	-69.648528
ngc2049	5.720919	-30.078389
ngc2050	5.610783	-69.383528
ngc2051	5.602039	-71.011389
ngc2052	5.619736	-69.774194
ngc2053	5.627694	-67.412917
ngc2054	5.754272	-10.083139
ngc2055	5.612425	-69.498639
ngc2056	5.609436	-70.671889
ngc2057	5.615317	-70.268944
ngc2058	5.615061	-70.16225
ngc2059	5.616819	-70.129028
ngc2060	5.629694	-69.171667
ngc2061	5.711603	-34.009528
ngc2062	5.667417	-66.87575
ngc2063	5.778619	8.781111
lbn939,ngc2064	5.771775	0.005944
ngc2065	5.627339	-70.236472
ngc2066	5.628644	-70.166556
ngc2067	5.775522	0.13125
m78,ngc2068	5.779394	0.079306
ngc2069	5.646233	-68.974389
30dorcluster,ngc2070,tarantulanebula	5.6451	-69.100889
lbn938,ngc2071	5.78535	0.29425
ngc2072	5.640108	-70.234056
ngc2073	5.764975	-21.999139
ngc2074	5.650994	-69.498111
ngc2075	5.639264	-70.685028
ngc2076	5.77985	-16.782611
ngc2077	5.660006	-69.657111
ngc2078	5.660958	-69.743167
ngc2079	5.660444	-69.757194
ngc2080	5.662728	-69.644111
ngc2081	5.666497	-69.405889
ngc2082	5.697533	-64.301139
ngc2083	5.66645	-69.737583
ngc2084	5.668611	-69.759417
ngc2085	5.669397	-69.672806
ngc2086	5.670244	-69.667861
ngc2087	5.737786	-55.532444
ngc2088	5.683281	-68.465361
ngc2089	5.797619	-17.602389
ngc2090	5.783858	-34.250611
ngc2091	5.682789	-69.437083
ngc2092	5.689444	-69.224222
ngc2093	5.69715	-68.921417
ngc2094	5.702458	-68.363778
ngc2095	5.710044	-67.318889
ngc2096	5.704944	-68.458611
ngc2097	5.737783	-62.785611
ngc2098	5.708619	-68.273167
m37,ngc2099	5.871764	32.553
ngc2100	5.702519	-69.211833
ngc2101	5.773381	-52.088528
ngc2102	5.705692	-69.487083
ngc2103	5.694542	-71.333139
ngc2104	5.784647	-51.552917
ngc2105	5.738661	-66.917611
ngc2106	5.846286	-21.56725
ngc2107	5.720244	-70.639944
ngc2108	5.732464	-69.182111
ngc2109	5.7397	-68.547806
ngc2110	5.869828	-7.456222
ngc2111	5.742497	-70.99325
ngc2112	5.895892	0.410806
ngc2113	5.756825	-69.774167
ngc2114	5.770031	-68.048306
ngc2115	5.85575	-50.5875
ngc2115a	5.855506	-50.582861
ngc2115b	5.855892	-50.5925
ngc2116	5.787544	-68.507944
ngc2117	5.796089	-67.450167
ngc2118	5.794325	-69.131833
ngc2119	5.957486	11.949194
ngc2120	5.842947	-63.677611
ngc2121	5.803567	-71.479778
ngc2122	5.814586	-70.070083
ngc2123	5.862033	-65.321472
ngc2124	5.964508	-20.084639
ngc2125	5.848397	-69.479139
ngc2126	6.042494	49.865917
ngc2127	5.855911	-69.359056
ngc2128	6.076175	57.62775
ngc2129	6.018483	23.322167
ngc2130	5.873256	-67.334111
ngc2131	5.979867	-26.653
ngc2132	5.928978	-59.927722
ngc2133	5.857978	-71.175028
ngc2134	5.866028	-71.097583
ngc2135	5.893175	-67.429528
ngc2136	5.882708	-69.49275
ngc2137	5.886986	-69.481972
ngc2138	5.913939	-65.837111
ngc2140	5.904494	-68.599833
ngc2141	6.048628	10.446472
ngc2142	6.030675	-10.597944
ngc2143	6.050433	5.831278
ngc2144	5.682553	-82.119389
ngc2145	5.906406	-70.901028
ngc2146	6.310475	78.357028
ngc2146a	6.398667	78.530111
ngc2147	5.929333	-68.201583
ngc2148	5.979403	-59.125944
ngc2149	6.058553	-9.730583
ngc2150	5.929539	-69.560806
ngc2151	5.939011	-69.017361
ngc2152	6.015358	-50.740917
ngc2153	5.964367	-66.400667
ngc2154	5.960414	-67.263778
ngc2155	5.975892	-65.476472
ngc2156	5.9638	-68.460806
ngc2157	5.959661	-69.197222
ngc2158	6.123781	24.096167
ngc2159	5.967744	-68.622917
ngc2160	5.970233	-68.289583
ngc2161	5.928628	-74.353944
ngc2162	6.008381	-63.721444
lbn855,ngc2163	6.130428	18.657444
ngc2164	5.982294	-68.515889
ngc2165	6.184503	51.677306
ngc2166	5.992817	-67.942333
ngc2167	6.116267	-6.202639
m35,ngc2168	6.151406	24.338639
ngc2169	6.140097	13.964861
lbn994,ngc2170	6.125506	-6.399306
ngc2171	5.983233	-70.719111
ngc2172	6.001622	-68.636917
ngc2173	5.966356	-72.974528
monkeyheadnebula,ngc2174	6.156561	20.659583
lbn854,ngc2175	6.160986	20.487583
ngc2176	6.02205	-66.85325
ngc2177	6.021247	-67.73325
ngc2178	6.04655	-63.763694
ngc2179	6.13395	-21.746694
ngc2180	6.160069	4.711611
ngc2181	6.045461	-65.264861
lbn998,ngc2182	6.158597	-6.326444
lbn996,ngc2183	6.179703	-6.211833
ngc2184	6.183242	-3.495167
lbn997,ngc2185	6.183464	-6.226861
ngc2186	6.201981	5.458583
ngc2187	6.063472	-69.583333
ngc2187a	6.062292	-69.588306
ngc2187b	6.064561	-69.577444
ngc2188	6.169314	-34.106194
ngc2189	6.202775	1.065972
ngc2190	6.017164	-74.725417
ngc2191	6.139964	-52.512306
ngc2192	6.254842	39.855222
ngc2193	6.104867	-65.098778
ngc2194	6.229419	12.806667
ngc2195	6.242725	17.639389
ngc2196	6.202681	-21.805944
ngc2197	6.102031	-67.097222
ngc2198	6.231919	0.994667
ngc2199	6.079153	-73.399833
ngc2200	6.22155	-43.663167
ngc2201	6.225447	-43.704722
ngc2202	6.280764	5.996167
ngc2203	6.078486	-75.438417
ngc2204	6.25895	-18.665861
ngc2205	6.175758	-62.538417
ngc2206	6.266622	-26.765472
ngc2207	6.272786	-21.372667
ngc2208	6.3763	51.909472
ngc2209	6.143308	-73.838417
ngc2210	6.192044	-69.121389
ngc2211	6.308433	-18.537278
ngc2212	6.309933	-18.519472
ngc2213	6.178317	-71.528444
ngc2214	6.215814	-68.260722
ngc2215	6.347014	-7.283778
ngc2216	6.358539	-22.087444
ngc2217	6.36105	-27.23375
ngc2218	6.411525	19.341306
ngc2219	6.395644	-4.677278
ngc2220	6.352989	-44.759778
ngc2221	6.3377	-57.578417
ngc2222	6.338072	-57.534472
ngc2223	6.409975	-22.83825
ngc2224	6.457942	12.593389
ngc2225	6.442914	-9.63075
ngc2226	6.443772	-9.642778
ngc2227	6.432772	-22.004833
ngc2228	6.354317	-64.458833
ngc2229	6.356578	-64.956667
ngc2230	6.357656	-64.992778
ngc2231	6.345269	-67.5185
ngc2232	6.466981	-4.847444
ngc2233	6.361128	-65.033361
ngc2234	6.489356	16.722861
ngc2235	6.372753	-64.934417
ngc2236	6.494361	6.830694
ngc2237,rosettea	6.515169	5.049167
lbn948,ngc2238,rosettenebula	6.511214	5.013056
ngc2239,ngc2244	6.5321	4.942944
ngc2240	6.552931	35.250194
ngc2241	6.380933	-68.925389
ngc2242	6.568678	44.777028
ngc2243	6.492911	-31.281333
lbn904,ngc2245	6.544792	10.156639
ngc2246,rosetteb	6.542722	5.128278
lbn901,ngc2247	6.551444	10.32225
ngc2248	6.576597	26.304444
ngc2249	6.430436	-68.919778
ngc2250	6.563856	-5.084444
ngc2251	6.577356	8.366389
ngc2252	6.578603	5.36625
ngc2253	6.728289	65.206278
ngc2254	6.597128	7.673278
ngc2255	6.566286	-34.812583
ngc2256	6.787214	74.236528
ngc2257	6.50385	-64.325611
ngc2258	6.796056	74.481667
ngc2259	6.639289	10.883611
ngc2260	6.634186	-1.472833
hubblesnebula,lbn920,ngc2261	6.652642	8.744333
ngc2262	6.660578	1.143639
ngc2263	6.641344	-24.848694
christmastreecluster,lbn911,ngc2264	6.682847	9.895472
ngc2265	6.6949	11.904639
ngc2266	6.722003	26.969556
ngc2267	6.681028	-32.482278
ngc2268	7.238178	84.382278
ngc2269	6.721411	4.624306
ngc2270	6.732711	3.4785
ngc2271	6.714719	-23.476
ngc2272	6.711472	-27.4595
ngc2273	6.835739	60.845806
ngc2273a	6.668636	60.080667
ngc2273b	6.775439	60.340389
ngc2274	6.788158	33.567194
ngc2275	6.788314	33.599222
ngc2276	7.453989	85.754556
ngc2277	6.796397	33.451278
ngc2278	6.804561	33.394306
ngc2279	6.806903	33.41525
ngc2280	6.746975	-27.638611
ngc2281	6.804956	41.078861
ngc2283	6.764636	-18.210333
ngc2284	6.819322	33.193806
ngc2285	6.826672	33.364667
ngc2286	6.794492	-3.147667
m41,ngc2287	6.76665	-20.754222
ngc2288	6.847767	33.462444
ngc2289	6.848225	33.478667
ngc2290	6.849144	33.437583
ngc2291	6.849622	33.525083
ngc2292	6.794347	-26.74625
ngc2293	6.795253	-26.754361
ngc2294	6.853139	33.527111
ngc2295	6.789839	-26.73625
ngc2297	6.740164	-63.717333
ngc2298	6.816444	-36.005306
ngc2299,ngc2302	6.864911	-7.082722
ngc2300	7.538881	85.7095
greatbirdcluster,ngc2301	6.862583	0.459194
ngc2303	6.938194	45.49275
ngc2304	6.919892	17.992778
ngc2305	6.810381	-64.273194
ngc2306	6.908211	-7.204139
ngc2307	6.814108	-64.335528
ngc2308	6.977108	45.210556
ngc2309	6.934336	-7.174306
ngc2310	6.898322	-40.862611
ngc2311	6.963208	-4.611333
ngc2312	6.97965	10.294472
ngc2313	6.967444	-7.945028
ngc2314	7.175708	75.326667
ngc2315	7.042517	50.590583
ngc2316	6.994681	-7.77775
ngc2317	6.994886	-7.7745
ngc2318	6.990839	-13.698389
ngc2319	7.008947	3.042194
ngc2320	7.095008	50.581056
ngc2321	7.099722	50.756028
ngc2322	7.100083	50.510306
m50,ngc2323	7.044575	-8.364028
ngc2324	7.068878	1.044611
ngc2325	7.044556	-28.697222
ngc2326	7.136394	50.681944
ngc2326a	7.142836	50.631389
ngc2327	7.068672	-11.314111
ngc2328	7.043389	-42.068556
ngc2329	7.152225	48.615417
ngc2331	7.116619	27.261583
ngc2332	7.159489	50.182278
ngc2333	7.139261	35.170028
ngc2335	7.113736	-10.028639
ngc2336	7.451125	80.178083
ngc2337	7.170439	44.457306
ngc2338	7.129825	-5.719722
ngc2339	7.139039	18.78025
ngc2340	7.186342	50.17475
ngc2341	7.153344	20.602917
ngc2342	7.155022	20.635972
ngc2343	7.135222	-10.616806
ngc2344	7.207961	47.166694
ngc2345	7.138553	-13.19375
ngc2346	7.156392	-0.809139
ngc2347	7.267692	64.708917
ngc2348	7.0507	-67.393944
ngc2349	7.180042	-8.59325
ngc2350	7.220053	12.266083
ngc2351	7.225564	-10.491417
ngc2352	7.218178	-24.046083
ngc2353	7.241753	-10.265861
ngc2354	7.234797	-25.688917
ngc2355,ngc2356	7.283128	13.749861
ngc2357	7.294719	23.35675
ngc2358	7.282314	-17.117083
lbn1041,ngc2359	7.308606	-13.227194
carolinescluster,ngc2360	7.295311	-15.641306
ngc2361	7.306611	-13.209556
ngc2362	7.311519	-24.954194
ngc2363	7.474886	69.192861
ngc2364	7.346242	-7.549722
ngc2365	7.372931	22.083278
ngc2366	7.48185	69.215778
ngc2367	7.334594	-21.884083
ngc2368	7.35175	-10.371778
ngc2369	7.277147	-62.343722
ngc2369a	7.312094	-62.936278
ngc2369b	7.341564	-62.053972
ngc2370	7.417128	23.783222
ngc2371,ngc2372	7.426294	29.490639
ngc2373	7.443597	33.823694
ngc2374	7.398908	-13.263361
ngc2375	7.452633	33.831806
ngc2376	7.443308	23.072944
ngc2377	7.415783	-9.659306
ngc2378	7.456722	33.831583
ngc2379	7.457294	33.81125
ngc2380,ngc2382	7.398542	-27.529056
ngc2381	7.332586	-63.067028
ngc2383	7.411083	-20.947639
ngc2384	7.419397	-21.019861
ngc2385	7.474464	33.837806
ngc2386	7.4772	33.773806
ngc2387	7.482758	36.879806
ngc2388	7.481511	33.819083
ngc2389	7.484625	33.860972
ngc2390	7.484519	33.836806
ngc2391	7.485414	33.825944
eskimonebula,ngc2392	7.486322	20.911833
ngc2393	7.501286	34.027778
ngc2394	7.476808	7.086556
ngc2395	7.453569	13.608194
ngc2396	7.467478	-11.719667
ngc2397	7.35555	-69.001472
ngc2397a	7.352197	-69.115333
ngc2397b	7.365436	-68.845806
ngc2398	7.504489	24.487889
ngc2399	7.497269	-0.214361
ngc2400	7.498572	-0.214722
ngc2401	7.490111	-13.966222
ngc2402	7.513111	9.650556
ngc2403	7.614278	65.602556
ngc2404	7.618536	65.610806
ngc2405	7.537217	25.906389
ngc2406	7.529928	18.287917
ngc2407	7.532408	18.333083
ngc2408	7.675533	71.668194
ngc2409	7.526867	-17.190417
ngc2410	7.583961	32.822111
ngc2411	7.576758	18.281556
ngc2412	7.572633	8.547778
ngc2413	7.554583	-13.095556
ngc2414	7.553556	-15.453861
ngc2415	7.615747	35.241972
ngc2416	7.594867	11.612028
ngc2417	7.503358	-62.252639
ngc2418	7.610419	17.883917
ngc2419	7.635542	38.879972
ngc2420	7.639972	21.574083
ngc2421	7.603281	-20.61225
m47,ngc2422,ngc2478	7.609728	-14.482611
ngc2423	7.618536	-13.8715
ngc2424	7.677581	39.233306
ngc2425	7.638231	-14.877833
ngc2426	7.721794	52.3185
ngc2427	7.607828	-47.635556
ngc2428	7.656047	-16.529028
ngc2429	7.730472	52.353056
ngc2429a	7.729883	52.357417
ngc2429b	7.731064	52.348472
ngc2430	7.661403	-16.296056
ngc2431,ngc2436	7.753719	53.075111
ngc2432	7.681631	-19.069083
ngc2433	7.712119	9.25925
ngc2434	7.580878	-69.284139
ngc2435	7.737106	31.651111
m46,ngc2437	7.696339	-14.81
ngc2438	7.697331	-14.735778
ngc2439	7.679281	-31.692417
ngc2440	7.698711	-18.208472
ngc2441	7.865206	73.015694
ngc2442,ngc2443	7.606622	-69.530833
ngc2444	7.7814	39.031861
ngc2445	7.781972	39.015167
ngc2446	7.8109	54.611917
m93,ngc2447	7.741453	-23.853083
ngc2448	7.742553	-24.673167
ngc2449	7.788967	26.930167
ngc2450	7.7923	27.019139
ngc2451	7.754169	-37.967444
ngc2452	7.790658	-27.334
ngc2453	7.792814	-27.194806
ngc2454	7.843061	16.368583
ngc2455	7.816278	-21.297944
ngc2456	7.902961	55.495306
ngc2457	7.912703	55.546556
ngc2458	7.930936	56.710611
ngc2459	7.867158	9.557417
ngc2460	7.947858	60.349389
ngc2461	7.940628	56.673306
ngc2462	7.942239	56.687111
ngc2463	7.953467	56.676528
ngc2464	7.959081	56.690556
ngc2465	7.95725	56.822472
ngc2466	7.754458	-71.410417
lbn1065,ngc2467	7.873175	-26.443333
ngc2468	7.96735	56.359583
ngc2469	7.967617	56.680472
ngc2470	7.905769	4.459694
ngc2471	7.975822	56.776167
ngc2472	7.978306	56.701306
ngc2473	7.926342	56.735806
ngc2474	7.966375	52.857278
ngc2475	7.966789	52.861694
ngc2476	7.945883	39.927889
ngc2477	7.869383	-38.53325
ngc2479	7.918353	-17.707806
ngc2480	7.9529	23.779806
ngc2481	7.953819	23.767778
ngc2482	7.919547	-24.254639
ngc2483	7.927442	-27.886833
ngc2484	7.974475	37.786611
ngc2485	7.94685	7.477944
ngc2486	7.965692	25.160861
ngc2487	7.97235	25.149222
ngc2488	8.029439	56.553861
ngc2489	7.937483	-30.060833
ngc2490	7.988297	27.077861
ngc2491	7.974272	7.983806
ngc2492	7.991586	27.026444
ngc2493	8.006564	39.830417
ngc2495	8.009208	39.840028
ngc2496	7.977042	8.029806
ngc2497	8.036425	56.942333
ngc2498	7.994125	24.982333
ngc2499	7.981031	7.493306
ngc2500	8.031447	50.737111
ngc2501	7.975011	-14.354278
ngc2502	7.930978	-52.306778
ngc2503	8.010189	22.400056
ngc2504	7.997861	5.608111
ngc2505	8.068567	53.549222
ngc2506	8.000494	-10.769639
ngc2507	8.027003	15.70975
ngc2508	8.032561	8.551889
ngc2509	8.013283	-19.050528
ngc2510	8.0363	9.485972
ngc2511	8.037503	9.394417
ngc2512	8.052181	23.391833
ngc2513	8.040186	9.413556
ngc2514	8.047122	15.808278
ngc2515	8.055914	20.188
ngc2516	7.968628	-60.753472
ngc2517	8.046408	-12.317833
ngc2518	8.122292	51.131611
ngc2519	8.133008	51.128222
ngc2520,ngc2527	8.082828	-28.146667
ngc2521	8.147047	57.769611
ngc2522	8.103733	17.706583
ngc2523	8.250025	73.578972
ngc2523a	8.069017	74.047778
ngc2523b	8.215858	73.56325
ngc2523c	8.295636	73.317611
ngc2524	8.135997	39.157444
ngc2525	8.0939	-11.427028
ngc2526	8.116286	8.003944
ngc2528	8.123564	39.194472
ngc2529	8.130308	17.820833
ngc2530	8.132114	17.8185
ngc2531	8.133639	17.820611
ngc2532	8.170883	33.956639
ngc2533	8.117806	-29.883861
ngc2534	8.215042	55.672056
ngc2535	8.187081	25.206806
ngc2536	8.187756	25.179361
bearclawnebula,bearpawgalaxy,ngc2537	8.220733	45.989806
ngc2537a	8.228064	45.99375
ngc2538	8.189742	3.633194
ngc2539	8.176939	-12.820667
ngc2540	8.2129	26.361778
ngc2541	8.244478	49.061722
ngc2542	8.187886	-12.927083
ngc2544	8.361206	73.988361
ngc2545	8.237267	21.355472
ngc2546	8.204342	-37.594306
ngc2547	8.169303	-49.205667
m48,ngc2548	8.228661	-5.750444
ngc2549	8.316208	57.803056
ngc2550	8.409406	74.012278
ngc2550a	8.477761	73.748
ngc2551	8.413967	73.412028
ngc2552	8.322369	50.009639
ngc2553	8.293056	20.903083
ngc2554	8.298192	23.472139
ngc2555	8.299003	0.745694
ngc2556	8.316903	20.936972
ngc2557	8.319653	21.435778
ngc2558	8.320211	20.51075
ngc2559	8.285019	-27.455833
ngc2560	8.331081	20.984972
ngc2561	8.326936	4.657222
ngc2562	8.339906	21.131472
ngc2563	8.343247	21.067806
ngc2564	8.308336	-21.816111
ngc2565	8.330089	22.031444
ngc2566	8.312683	-25.499528
ngc2567	8.309772	-30.635611
ngc2568	8.305033	-37.105389
ngc2569	8.355872	20.8675
ngc2570	8.356261	20.910556
ngc2571	8.315653	-29.749278
ngc2572	8.356842	19.147778
ngc2573,polarissimaaustralis	1.693703	-89.334528
ngc2573b	23.125783	-89.1165
ngc2574	8.346711	-8.918472
ngc2575	8.379156	24.296917
ngc2576	8.382694	25.738722
ngc2577	8.378736	22.553083
ngc2578	8.356742	-13.317861
ngc2579	8.348072	-36.217139
ngc2580	8.35775	-30.293472
ngc2581	8.408594	18.597083
ngc2583	8.385536	-5.002389
ngc2584	8.387625	-4.9705
ngc2585	8.390633	-4.915222
ngc2586	8.392058	-4.951944
ngc2587	8.390022	-29.508722
ngc2588	8.385992	-32.975167
ngc2589	8.408186	-8.767917
ngc2591	8.623758	78.026417
ngc2592	8.452236	25.970306
ngc2593	8.446619	17.374917
ngc2594	8.454767	25.878806
ngc2595	8.461672	21.479111
ngc2596	8.457367	17.284083
ngc2597	8.499281	21.501889
ngc2598	8.5007	21.488667
ngc2599	8.536472	22.560556
ngc2600	8.579181	52.715694
ngc2601	8.425183	-68.117667
ngc2602	8.584514	52.831528
ngc2603	8.575331	52.840222
ngc2604	8.556428	29.538806
ngc2604b	8.559906	29.499694
ngc2605	8.581475	52.804306
ngc2606	8.5929	52.788917
ngc2607	8.565739	26.972667
ngc2608	8.588147	28.473417
ngc2609	8.491569	-61.110222
ngc2610	8.5565	-16.149444
ngc2611	8.591436	25.0275
ngc2612	8.563917	-13.174528
ngc2613	8.556344	-22.973667
ngc2614	8.713319	72.976472
ngc2615	8.575931	-2.546806
ngc2616	8.592797	-1.850139
ngc2617	8.594108	-4.088222
ngc2618	8.598206	0.707111
ngc2619	8.625753	28.705194
ngc2620	8.624511	24.946944
ngc2621	8.626939	24.999806
ngc2622	8.636372	24.895278
ngc2623	8.640022	25.754639
ngc2624	8.636008	19.725667
ngc2625	8.639783	19.716667
ngc2626	8.591356	-40.668333
ngc2627	8.620817	-29.950417
ngc2628	8.672975	23.539667
ngc2629	8.787728	72.985639
ngc2630,ngc2631	8.785361	73.000306
beehive,m44,ngc2632,praesepecluster	8.672833	19.672056
ngc2633	8.801272	74.098861
ngc2634	8.807053	73.967167
ngc2634a	8.810594	73.939278
ngc2635	8.640553	-34.771583
ngc2636	8.806786	73.671139
ngc2637	8.687081	19.691444
ngc2638	8.707158	37.221028
ngc2639	8.727244	50.205556
ngc2640	8.623506	-55.12375
ngc2641	8.799303	72.895778
ngc2642	8.678992	-4.121722
ngc2644	8.692183	4.980333
ngc2645	8.650867	-46.227306
ngc2646	8.839458	73.463083
ngc2647	8.711972	19.650611
ngc2648	8.711056	14.285611
ngc2649	8.735631	34.71725
ngc2650	8.832875	70.299444
ngc2651	8.731986	11.771
ngc2652,ngc2974	9.709244	-3.699139
ngc2653	8.915433	78.393556
ngc2654	8.819964	60.221111
ngc2655	8.927147	78.223083
ngc2656	8.798075	53.876167
ngc2657	8.754392	9.6455
ngc2658	8.724261	-32.656222
ngc2659	8.709172	-45.000528
ngc2660	8.710553	-47.200667
ngc2661	8.766539	12.619917
ngc2662	8.758897	-15.12125
ngc2663	8.752292	-33.79475
ngc2664	8.785286	12.605778
ngc2665	8.766942	-19.302889
ngc2666	8.829728	44.703667
ngc2668	8.822933	36.710333
ngc2669	8.772936	-52.947528
ngc2670	8.758189	-48.791639
ngc2671	8.769969	-41.877167
ngc2672	8.822747	19.074972
ngc2673	8.823372	19.074194
ngc2674	8.820336	-14.294222
ngc2675	8.868042	53.617306
ngc2676	8.859903	47.557667
ngc2677	8.833703	19.009778
ngc2678	8.834097	11.338111
ngc2679	8.85915	30.865361
ngc2680	8.859303	30.865806
ngc2681	8.892428	51.313667
m67,ngc2682	8.855592	11.811944
ngc2683	8.878147	33.42175
ngc2684	8.915011	49.160389
helixgalaxy,ngc2685	8.926308	58.734389
ngc2686	8.916611	49.142361
ngc2686a	8.916364	49.142333
ngc2686b	8.916831	49.142444
ngc2687	8.918194	49.155917
ngc2687a	8.918061	49.1565
ngc2687b	8.918344	49.156111
ngc2688	8.919886	49.122611
ngc2689	8.923725	49.115472
ngc2690	8.877231	-2.603222
ngc2691	8.912872	39.538667
ngc2692	8.949447	52.065944
ngc2693	8.949797	51.347444
ngc2694	8.949794	51.331972
ngc2695	8.907519	-3.067028
ngc2696	8.845014	-5.009778
ngc2697	8.9165	-2.987611
ngc2698	8.926808	-3.183944
ngc2699	8.930222	-3.127583
ngc2700	8.930717	-3.116389
ngc2701	8.984928	53.771667
ngc2702	8.931844	-3.065333
ngc2703	8.929758	-3.306917
ngc2705	8.933347	-3.014889
ngc2706	8.936753	-2.563444
ngc2707	8.934911	-3.066417
ngc2708,ngc2727	8.935569	-3.360111
ngc2709	8.936906	-3.243222
ngc2710	8.996764	55.706389
ngc2711	8.956556	17.288028
ngc2712	8.991797	44.913889
ngc2713	8.955697	2.921306
ngc2714	8.891617	-59.217111
ngc2715	9.135056	78.085167
ngc2716	8.959967	3.090222
ngc2717	8.950311	-24.67375
ngc2718	8.980686	6.293
ngc2719	9.004294	35.727639
ngc2719a	9.004428	35.720139
ngc2720	8.985572	11.149222
ngc2721	8.982367	-4.901944
ngc2722,ngc2733	8.979492	-3.710111
ngc2723	9.003989	3.17775
ngc2724	9.017172	35.762056
ngc2725	9.017561	11.098389
ngc2726	9.082436	59.932917
ngc2728	9.028036	11.082972
ngc2729	9.024617	3.720611
ngc2730	9.037731	16.838306
ngc2731	9.035669	8.301667
ngc2732	9.223536	79.187333
ngc2734	9.050447	16.863611
ngc2735	9.044067	25.934528
ngc2735a	9.044964	25.938389
ngc2736,pencilnebula	9.004706	-45.948056
ngc2737	9.066589	21.906556
ngc2738	9.066792	21.967611
ngc2739	9.100786	51.744694
ngc2740	9.101386	51.735306
ngc2741	9.054583	18.261083
ngc2742	9.125981	60.479333
ngc2742a	9.166131	62.247361
ngc2743	9.081683	25.003917
ngc2744	9.077472	18.460278
ngc2745	9.077592	18.257361
ngc2746	9.099844	35.377389
ngc2747	9.088428	18.442194
ngc2748	9.228617	76.475333
ngc2749	9.089256	18.313111
ngc2750	9.096642	25.437417
ngc2751	9.092333	18.262306
ngc2752	9.095286	18.339722
ngc2753	9.118961	25.342472
ngc2754	9.086447	-19.084861
ngc2755	9.132864	41.708944
ngc2756	9.150258	53.849528
ngc2757	9.090489	-19.047806
ngc2758	9.092	-19.042778
ngc2759	9.143692	37.621611
ngc2760	9.403622	76.531278
ngc2761	9.125231	18.43475
ngc2762	9.165147	50.41825
ngc2763	9.113625	-15.499778
ngc2764	9.138186	21.443333
ngc2765	9.126844	3.392917
ngc2766	9.146539	29.864778
ngc2767	9.169967	50.401306
ngc2768	9.19375	60.037222
ngc2769	9.1756	50.433278
ngc2770	9.159364	33.123528
ngc2771	9.177683	50.379861
ngc2772	9.128297	-23.621417
ngc2773	9.162275	7.173694
ngc2774	9.177756	18.696583
ngc2775	9.172256	7.037944
ngc2776	9.204031	44.954833
ngc2777	9.178286	7.206694
ngc2778	9.206769	35.027528
ngc2779	9.207858	35.05375
ngc2780	9.212325	34.925583
ngc2781	9.190978	-14.816833
ngc2782	9.234753	40.113694
ngc2783	9.227628	29.992972
ngc2784	9.205417	-24.172611
ngc2785	9.254275	40.917528
ngc2786	9.226553	12.440806
ngc2787	9.321833	69.20325
ngc2788	9.150844	-67.932472
ngc2788a	9.044289	-68.226833
ngc2788b	9.059917	-67.969806
ngc2789	9.249906	29.730278
ngc2790	9.250772	19.697111
ngc2791	9.250553	17.592222
ngc2792	9.207381	-42.4275
ngc2793	9.279808	34.429806
ngc2794	9.267164	17.589833
ngc2795	9.267756	17.628361
ngc2796	9.278292	30.915417
ngc2797	9.272692	17.727222
ngc2798	9.289664	41.999722
ngc2799	9.291953	41.994083
ngc2800	9.309783	52.514472
ngc2801	9.278942	19.935722
ngc2802	9.278175	18.963472
ngc2803	9.278853	18.954583
ngc2805	9.339003	64.102778
ngc2806	9.282442	20.070611
ngc2807	9.283056	20.032222
ngc2807a	9.282689	20.029056
ngc2807b	9.283517	20.0365
ngc2808	9.200706	-64.862833
ngc2809	9.285256	20.069694
ngc2810	9.367917	71.844028
ngc2811	9.269753	-16.312722
ngc2812	9.294664	19.918889
ngc2813	9.295958	19.906611
ngc2814	9.353189	64.253194
ngc2815	9.272153	-23.63325
ngc2816,ngc2820	9.362661	64.257944
ngc2817	9.286258	-4.752111
ngc2818	9.267083	-36.626944
ngc2818a	9.268369	-36.626917
ngc2819	9.302581	16.198111
ngc2820a	9.358353	64.238722
ngc2821	9.279994	-26.816278
ngc2822	9.230478	-69.644833
ngc2823	9.321517	34.008167
ngc2824	9.317286	26.269972
ngc2825	9.3229	33.742778
ngc2826	9.323381	33.624
ngc2828	9.326342	33.888083
ngc2829	9.325194	33.648333
ngc2830	9.328169	33.738139
ngc2831	9.329303	33.745
ngc2832	9.329683	33.74975
ngc2833	9.332739	33.927444
ngc2834	9.334033	33.710472
ngc2835	9.298031	-22.354667
ngc2836	9.229056	-69.33475
ngc2837	9.306492	-16.481722
ngc2838	9.345289	39.31575
ngc2839	9.343425	33.650667
ngc2840	9.347978	35.368278
ngc2841	9.367397	50.976528
ngc2842	9.260119	-63.069639
ngc2843	9.341328	18.926222
ngc2844	9.363336	40.15125
ngc2845	9.310197	-38.010083
ngc2846	9.327908	-14.676278
ngc2847	9.335703	-16.518306
ngc2848	9.336064	-16.526056
ngc2849	9.323019	-40.520389
ngc2850	9.349169	-4.940083
ngc2851	9.341731	-16.495278
ngc2852	9.387386	40.163806
ngc2853	9.388147	40.200056
ngc2854	9.400864	49.204139
ngc2855	9.357636	-11.9095
ngc2856	9.404447	49.249194
ngc2857	9.410478	49.357056
ngc2858	9.381947	3.156944
ngc2859	9.405147	34.5135
ngc2860	9.414781	41.060194
ngc2861	9.393472	2.136472
ngc2862	9.415308	26.774667
ngc2863,ngc2869	9.393489	-10.433222
ngc2864	9.404275	5.941167
ngc2865	9.391725	-23.161444
ngc2866	9.368067	-51.102611
ngc2867	9.356936	-58.311667
ngc2868	9.390894	-10.4295
ngc2870	9.464928	57.3755
ngc2871	9.42765	11.444333
ngc2872	9.428483	11.432139
ngc2873	9.430139	11.454222
ngc2874	9.429814	11.424583
ngc2875	9.430225	11.431639
ngc2876	9.420492	-6.716583
ngc2877	9.429717	2.229111
ngc2878	9.42985	2.089611
ngc2879	9.422922	-11.6515
ngc2880	9.492933	62.490556
ngc2881	9.431722	-11.993889
ngc2882	9.443372	7.954472
ngc2883	9.421783	-34.10325
ngc2884	9.440125	-11.555583
ngc2886	9.444083	-21.737806
ngc2887	9.390014	-63.812556
ngc2888	9.438797	-28.035083
ngc2889	9.453497	-11.643417
ngc2890	9.441622	-14.528694
ngc2891	9.449064	-24.783028
ngc2892	9.548036	67.617389
ngc2893	9.504711	29.539972
ngc2894	9.491733	7.718833
ngc2895	9.540292	57.482889
ngc2896	9.504714	23.663056
ngc2897	9.496033	2.206806
ngc2898	9.496206	2.064361
ngc2899	9.450822	-56.106028
ngc2900	9.504219	4.144222
ngc2901	9.542847	31.111694
ngc2902	9.514692	-14.735778
ngc2903,ngc2905	9.536142	21.500833
ngc2904	9.504722	-30.385028
ngc2906	9.535061	8.441778
ngc2907	9.526867	-16.734667
ngc2908	9.725403	79.70125
ngc2909	9.616639	65.940556
ngc2910	9.508061	-52.914
ngc2911	9.562808	10.152444
ngc2912	9.5658	10.192222
ngc2913	9.567422	9.479194
ngc2914	9.567439	10.108583
ngc2915	9.436536	-76.626333
ngc2916	9.582667	21.705278
ngc2917	9.574139	-2.504167
ngc2918	9.595567	31.705472
ngc2919	9.579867	10.283722
ngc2920	9.570069	-20.859056
ngc2921	9.575444	-20.920361
ngc2922	9.614575	37.694889
ngc2923	9.601064	16.760389
ngc2924	9.586336	-16.398389
ngc2925	9.553033	-53.395972
ngc2926	9.625281	32.841417
ngc2927	9.620889	23.590611
ngc2928	9.619467	16.977194
ngc2929	9.624947	23.161667
ngc2930	9.625722	23.2025
ngc2931	9.627125	23.24075
ngc2932	9.597672	-46.9245
ngc2933	9.631944	17.014722
ngc2934	9.631989	17.0545
ngc2935	9.612458	-21.128139
ngc2936	9.628931	2.760806
ngc2937	9.629175	2.747361
ngc2938	9.639942	76.319556
ngc2939	9.635575	9.521528
ngc2940	9.634775	9.616722
ngc2941	9.640058	17.044444
ngc2942	9.652211	34.006333
ngc2943	9.642464	17.031306
ngc2944	9.655056	32.308333
ngc2945	9.628092	-22.035056
ngc2946	9.650439	17.025333
ngc2948	9.649775	6.955444
ngc2949	9.665625	16.787444
ngc2950	9.709764	58.851278
ngc2951	9.661222	-0.235278
ngc2952	9.626942	-10.183389
ngc2953	9.671956	14.832694
ngc2954	9.673353	14.922639
ngc2955	9.68795	35.882278
ngc2956	9.654736	-19.101083
ngc2957	9.788028	72.985
ngc2957a	9.788333	72.984083
ngc2958	9.678228	11.888417
ngc2959	9.752492	68.594583
ngc2960	9.676772	3.577
ngc2961	9.756242	68.608278
ngc2962	9.681647	5.165806
ngc2963	9.797339	72.964389
ngc2964	9.715064	31.847389
ngc2965	9.721986	36.247806
ngc2966	9.703189	4.673139
ngc2967	9.700914	0.336444
ngc2968	9.720003	31.928694
ngc2969	9.698472	-8.603
ngc2970	9.725297	31.976972
ngc2971	9.729478	36.179361
ngc2972,ngc2999	9.669867	-50.320944
ngc2973	9.692986	-30.048389
ngc2975	9.687797	-16.674389
ngc2976	9.787628	67.916389
ngc2977	9.729525	74.860222
ngc2978	9.721333	-9.745889
ngc2979,ngc3050	9.719069	-10.38325
ngc2980	9.719992	-9.612389
ngc2981	9.749047	31.097833
ngc2982	9.700022	-44.027139
ngc2983	9.728083	-20.477194
ngc2985	9.839508	72.278639
ngc2986	9.737789	-21.278
ngc2987	9.761519	4.941833
ngc2988	9.779992	22.012139
ngc2989	9.757006	-18.373917
ngc2990	9.771433	5.708806
ngc2991	9.780589	22.013944
ngc2992	9.761681	-14.326389
ngc2993	9.763425	-14.368306
ngc2994	9.787808	22.0895
ngc2995	9.733081	-54.596944
ngc2996	9.77505	-21.571611
ngc2997	9.760775	-31.191083
ngc2998	9.812119	44.081444
ngc3000	9.814244	44.130278
ngc3001	9.77185	-30.437472
ngc3002	9.81595	44.057222
ngc3003	9.810014	33.4215
ngc3004	9.817347	44.111028
ngc3005	9.820797	44.131306
ngc3006	9.821483	44.025806
ngc3007	9.796006	-6.438167
ngc3008	9.826183	44.102694
ngc3009	9.836425	44.295056
ngc3010	9.842542	44.314389
ngc3010a	9.842936	44.323417
ngc3010c	9.844275	44.330972
ngc3011	9.828111	32.221111
ngc3012	9.831142	34.714111
ngc3013	9.835933	33.569333
ngc3014	9.818792	-4.742944
ngc3015	9.823033	1.145417
ngc3016	9.830739	12.695222
ngc3017	9.817511	-2.821806
ngc3018	9.828181	0.62125
ngc3019	9.835336	12.746139
ngc3020	9.835167	12.813639
ngc3021	9.849208	33.553639
ngc3022	9.827569	-5.166583
ngc3023	9.831275	0.618167
ngc3024	9.840942	12.7655
ngc3025	9.824739	-21.74225
ngc3026	9.848714	28.551111
ngc3027	9.927944	72.203556
ngc3028	9.831733	-19.184167
ngc3029	9.815006	-8.050944
ngc3030	9.836256	-12.226417
bodesgalaxy,m81,ngc3031	9.925881	69.065306
ngc3032	9.868931	29.236222
ngc3033	9.809733	-56.430056
cigargalaxy,m82,ngc3034	9.931314	69.679389
ngc3035	9.865286	-6.822917
ngc3036	9.821081	-62.675583
ngc3037	9.856672	-27.011111
ngc3038	9.854292	-32.752556
ngc3039	9.874908	2.154444
ngc3040	9.884528	19.437222
ngc3041	9.885317	16.677667
ngc3042	9.88895	0.697694
ngc3043	9.937458	59.307111
ngc3044	9.894689	1.579639
ngc3045	9.888239	-18.645111
ngc3046,ngc3051	9.899622	-27.286333
ngc3047	9.908528	-1.289722
ngc3047a	9.908906	-1.290917
ngc3047b	9.908192	-1.288056
ngc3048	9.915889	16.457778
ngc3049	9.913767	9.271083
ngc3052	9.907758	-18.638889
ngc3053	9.926003	16.432861
ngc3054	9.907944	-25.703444
ngc3055	9.921683	4.270028
ngc3056	9.909133	-28.298194
ngc3057	10.094267	80.285694
ngc3058	9.893264	-12.481556
ngc3059	9.8356	-73.922194
ngc3060	9.938667	16.831222
ngc3061	9.936669	75.8665
ngc3062	9.943275	1.428556
ngc3063	10.028269	72.117833
ngc3064	9.928181	-6.363917
ngc3065	10.032006	72.170333
ngc3066	10.036408	72.125389
ngc3067	9.972522	32.369889
ngc3068	9.977806	28.877556
ngc3070	9.968597	10.359778
ngc3071	9.981386	31.620306
ngc3072	9.956636	-19.354972
ngc3073	10.014467	55.618833
ngc3074	9.994781	35.392806
ngc3075	9.982278	14.420472
ngc3076	9.96045	-18.178694
ngc3077	10.055297	68.733917
ngc3078	9.973503	-26.926667
ngc3079	10.032722	55.679778
ngc3080	9.998844	13.043833
ngc3082	9.981408	-30.357694
ngc3083	9.997131	-2.877472
ngc3085	9.991439	-19.492278
ngc3086	10.003053	-2.976167
ngc3087	9.985739	-34.225222
ngc3088	10.019194	22.403611
ngc3088a	10.018664	22.403167
ngc3088b	10.019361	22.402306
ngc3089	9.993522	-28.331361
ngc3090	10.008397	-2.969
ngc3091	10.003969	-19.636972
ngc3092	10.013175	-3.012389
ngc3093	10.014886	-2.972
ngc3094	10.023872	15.770083
ngc3095	10.001619	-31.552861
ngc3096	10.009197	-19.661972
ngc3097	10.071131	60.125778
ngc3098	10.037969	24.711083
ngc3099	10.043486	32.706722
ngc3100,ngc3103	10.011344	-31.664528
ngc3101	10.026508	-2.994417
ngc3102	10.075489	60.107972
ngc3104	10.065931	40.756917
ngc3105	10.010978	-54.787694
ngc3106	10.068125	31.185472
ngc3107	10.072908	13.621333
ngc3108	10.041397	-31.677417
ngc3109	10.051911	-26.159583
ngc3110,ngc3122,ngc3518	10.067253	-6.474778
ngc3111	10.102067	47.262639
ngc3112	10.066439	-20.781806
ngc3113	10.073919	-28.444028
ngc3114	10.041547	-60.130528
ngc3115,spindlegalaxy	10.087217	-7.718583
ngc3116	10.112514	31.097722
ngc3117	10.102917	2.912861
ngc3118	10.119872	33.027389
ngc3119,ngc3121	10.114408	14.373528
ngc3120	10.089733	-34.219944
ngc3123	10.117181	0.067139
ngc3124	10.111083	-19.221583
ngc3125	10.109269	-29.934861
ngc3126	10.139072	31.862694
ngc3127	10.106903	-16.126083
ngc3128	10.100381	-16.122028
ngc3129	10.138683	18.430639
ngc3130	10.136761	9.977
ngc3131	10.143447	18.231222
eightburstnebula,ngc3132	10.117147	-40.436583
ngc3133	10.120225	-11.965306
ngc3134	10.208136	12.37725
ngc3135	10.181772	45.950361
ngc3136	10.096711	-67.377972
ngc3136a	10.05905	-67.448472
ngc3136b	10.170258	-67.005083
ngc3137	10.152078	-29.064306
ngc3138	10.154631	-11.95675
ngc3139	10.168106	-11.77825
ngc3140	10.157728	-16.628167
ngc3141	10.155525	-16.653417
ngc3142	10.168436	-8.47975
ngc3143	10.167772	-12.581361
ngc3144,ngc3174	10.258939	74.220278
ngc3145	10.169408	-12.433778
ngc3146	10.186075	-20.870694
ngc3147	10.281569	73.40075
ngc3148	10.228842	50.496528
ngc3149	10.062247	-80.421667
ngc3150	10.223978	38.657667
ngc3151	10.224747	38.619833
ngc3152	10.226144	38.843194
ngc3153	10.214028	12.666667
ngc3154	10.217022	17.034167
ngc3155,ngc3194	10.294403	74.347389
ngc3156	10.211458	3.129361
ngc3158	10.2307	38.764889
ngc3159	10.231342	38.654472
ngc3160	10.231964	38.842833
ngc3161	10.233111	38.657139
ngc3162,ngc3575	10.225442	22.737556
ngc3163	10.235306	38.652556
ngc3164	10.253172	56.672083
ngc3165	10.225361	3.375028
ngc3166	10.229333	3.424722
ngc3167	10.243303	29.596333
ngc3168	10.273058	60.234944
ngc3169	10.237514	3.466083
ngc3170	10.270703	46.612361
ngc3171	10.260228	-20.647389
ngc3172,polarissimaborealis	11.787222	89.093056
ngc3173	10.243019	-27.692833
ngc3175	10.245031	-28.872056
ngc3176	10.254872	-19.032556
ngc3177	10.27615	21.123056
ngc3178	10.269214	-15.791278
ngc3179	10.299225	41.114306
ngc3180	10.302686	41.445028
ngc3181	10.303197	41.412694
ngc3182	10.325839	58.205722
ngc3183,ngc3218	10.363611	74.176861
ngc3184	10.304683	41.424056
ngc3185	10.294047	21.68825
ngc3186	10.264831	6.96375
ngc3187	10.296628	21.873333
ngc3188	10.328558	57.423472
ngc3188a	10.3273	57.418583
ngc3189,ngc3190	10.301564	21.832306
ngc3191,ngc3192	10.318092	46.454111
ngc3193	10.306917	21.893972
ngc3195	10.155828	-80.858583
ngc3196	10.313619	27.668944
ngc3197	10.241019	77.82025
ngc3198	10.331931	45.549611
ngc3199	10.290119	-57.922222
ngc3200	10.310153	-17.982528
ngc3201	10.293544	-46.411222
ngc3202	10.34215	43.021611
ngc3203	10.326064	-26.698889
ngc3204	10.336411	27.817056
ngc3205	10.347214	42.972056
ngc3206	10.363219	56.930417
ngc3207	10.350153	42.985306
ngc3208	10.328136	-25.81475
ngc3209	10.344006	25.504972
ngc3210	10.466444	79.832528
ngc3211	10.297364	-62.670056
ngc3212	10.471239	79.823389
ngc3213	10.354819	19.651778
ngc3214	10.385775	57.039083
ngc3215	10.477939	79.813083
ngc3216	10.361453	23.923056
ngc3219	10.377067	38.579167
ngc3221	10.372217	21.569583
ngc3222	10.376253	19.887028
ngc3224	10.361442	-34.696778
ngc3225	10.419417	58.15
ngc3226	10.390836	19.898528
ngc3227	10.391828	19.865056
ngc3228	10.356178	-51.722583
ngc3229	10.3901	0.064806
ngc3230	10.395544	12.567778
ngc3231	10.449403	66.815167
ngc3232	10.406731	28.026139
ngc3233	10.365961	-22.26775
ngc3234,ngc3235	10.416475	28.023917
ngc3236	10.446808	61.272917
ngc3237	10.428694	39.646389
ngc3238	10.445275	57.226333
ngc3239	10.418025	17.163583
ngc3240	10.408508	-21.791028
ngc3241	10.404711	-32.482611
jupitersghostnebula,ngc3242	10.4128	-18.642222
ngc3243	10.439297	-2.622194
ngc3244	10.424678	-39.827556
ngc3245	10.455108	28.507444
ngc3245a	10.450314	28.639333
ngc3246	10.444947	3.861917
ngc3247	10.403889	-57.763333
ngc3248	10.462622	22.847194
ngc3249	10.439503	-34.963694
ngc3250	10.4423	-39.943944
ngc3250a	10.464925	-40.081333
ngc3250b	10.462436	-40.435028
ngc3250c	10.461797	-40.002583
ngc3250d	10.466094	-39.814778
ngc3250e	10.483528	-40.082806
ngc3252	10.573094	73.764972
ngc3253	10.474256	12.704056
ngc3254	10.488872	29.491833
ngc3255	10.442044	-60.675194
ngc3256	10.464242	-43.90375
ngc3256a	10.430844	-43.748083
ngc3256b	10.483631	-44.402889
ngc3256c	10.484928	-43.849278
ngc3257	10.479756	-35.658083
ngc3258	10.481547	-35.605528
ngc3258a	10.471989	-35.454472
ngc3258b	10.507028	-35.563556
ngc3258c	10.523375	-35.220472
ngc3258d	10.532147	-35.409806
ngc3258e	10.540253	-34.998361
ngc3259	10.543014	65.041083
ngc3260	10.485108	-35.595194
ngc3261	10.483739	-44.656833
ngc3262	10.485064	-44.159667
ngc3263	10.487044	-44.122917
ngc3264	10.538806	56.085278
ngc3265	10.518547	28.796667
ngc3266	10.554892	64.749389
ngc3267	10.496831	-35.322389
ngc3268	10.500183	-35.325472
ngc3269	10.499183	-35.224389
ngc3270	10.524994	24.869444
ngc3272	10.530042	28.468778
ngc3273	10.508103	-35.610639
ngc3274	10.538131	27.668778
ngc3275	10.514389	-36.736972
ngc3276	10.519222	-39.944667
ngc3277	10.548736	28.511722
ngc3278	10.526497	-39.954639
ngc3280,ngc3295	10.545908	-12.63625
ngc3280a	10.546217	-12.634583
ngc3280c	10.545986	-12.637222
ngc3281	10.531136	-34.853694
ngc3281a	10.532856	-35.1985
ngc3281b	10.531156	-35.204861
ngc3281c	10.549875	-34.886222
ngc3281d	10.57195	-34.403417
ngc3282	10.539422	-22.302278
ngc3283	10.519889	-46.251278
ngc3284,ngc3286	10.6059	58.620167
ngc3285	10.559956	-27.454444
ngc3285a	10.546883	-27.522444
ngc3285b	10.576911	-27.652944
ngc3287	10.579806	21.648278
ngc3288	10.607131	58.556194
ngc3289	10.568731	-35.323389
ngc3290	10.588175	-17.276778
ngc3291	10.6018	37.274417
ngc3292	10.592897	-6.179611
ngc3293	10.596881	-58.224472
ngc3294	10.604514	37.324694
ngc3297	10.553278	-12.671833
ngc3298	10.620078	50.120583
ngc3299	10.606611	12.707389
ngc3300	10.610678	14.171111
ngc3301,ngc3760	10.615567	21.882139
ngc3302	10.596508	-32.3585
ngc3303	10.616611	18.136667
ngc3304	10.627197	37.455639
ngc3305	10.603264	-27.162194
ngc3306	10.619506	12.652472
ngc3307	10.604769	-27.52975
ngc3308	10.606222	-27.438139
ngc3309	10.609917	-27.518444
ngc3310	10.646072	53.503389
ngc3311	10.611894	-27.528333
ngc3313	10.623736	-25.319444
ngc3314	10.620333	-27.684444
ngc3314a	10.620236	-27.683944
ngc3314b	10.620347	-27.684972
ngc3315	10.622008	-27.192306
ngc3316	10.627033	-27.594306
ngc3317	10.628642	-27.519611
ngc3318	10.620975	-41.627556
ngc3318a	10.59225	-41.740944
ngc3318b	10.626067	-41.465389
ngc3319	10.652628	41.686667
ngc3320	10.660147	47.397917
ngc3321,ngc3322	10.647378	-11.648861
ngc3323	10.660844	25.32275
ngc3324	10.621169	-58.619556
ngc3325	10.655681	-0.20025
ngc3326	10.65885	5.107611
ngc3327	10.666094	24.09125
ngc3328	10.665069	9.300111
ngc3329,ngc3397	10.744269	76.809444
ngc3330	10.645953	-54.130722
ngc3331	10.66915	-23.820361
ngc3332,ngc3342	10.674547	9.182556
ngc3333	10.663842	-36.036167
ngc3334	10.692	37.312861
ngc3335	10.659461	-23.922694
ngc3336	10.671394	-27.777083
ngc3337	10.696553	4.988389
ngc3338	10.702094	13.747
ngc3339	10.702794	-0.36925
ngc3340	10.704997	-0.376861
ngc3341	10.708742	5.043806
ngc3343	10.769569	73.353139
ngc3344	10.725319	24.922222
ngc3345	10.725561	11.985278
ngc3346	10.727475	14.871861
ngc3347	10.712931	-36.352667
ngc3347a	10.672392	-36.411111
ngc3347b	10.69995	-36.935333
ngc3347c	10.681581	-36.287917
ngc3348	10.786111	72.839667
ngc3349	10.730711	6.762972
ngc3350	10.739714	30.724861
m95,ngc3351	10.732694	11.703806
ngc3352	10.737481	22.371194
ngc3353	10.756225	55.960389
ngc3354	10.717483	-36.362389
ngc3355	10.690553	-23.38425
ngc3356	10.736731	6.758778
ngc3357	10.739094	14.084472
ngc3358	10.725839	-36.410694
ngc3359	10.776906	63.224222
ngc3360	10.737828	-11.242556
ngc3361	10.741436	-11.207917
ngc3362	10.7477	6.596722
ngc3363	10.752628	22.0785
ngc3364	10.808283	72.425028
ngc3365	10.770164	1.813278
ngc3367	10.776375	13.750861
m96,ngc3368	10.779372	11.819944
ngc3369	10.779069	-25.244444
ngc3370	10.784458	17.273611
ngc3371,ngc3384	10.804692	12.629278
carinanebula,etacarnebula,ngc3372	10.752369	-59.866694
ngc3373,ngc3389	10.807753	12.533194
ngc3374	10.800292	43.186556
ngc3375	10.783553	-9.941306
ngc3376	10.790714	6.048139
ngc3377	10.795092	13.985917
ngc3377a	10.789528	14.069444
ngc3378	10.778686	-40.016028
m105,ngc3379	10.797108	12.581611
ngc3380	10.803383	28.601778
ngc3381	10.806894	34.711417
ngc3382	10.806953	36.725444
ngc3383	10.788667	-24.438167
ngc3385	10.803231	4.92775
ngc3386	10.803308	4.998583
ngc3387	10.80465	4.966611
ngc3388,ngc3425	10.857092	8.567139
ngc3390	10.801211	-31.533361
ngc3391	10.815656	14.219833
ngc3392	10.850833	65.781556
ngc3393	10.806517	-25.162056
ngc3394	10.8444	65.727222
ngc3396	10.831964	32.990833
ngc3399	10.824333	16.218556
ngc3400	10.845964	28.469083
ngc3401	10.838853	5.8115
ngc3402,ngc3411	10.840686	-12.844611
ngc3403	10.898572	73.690361
ngc3405	10.828833	16.240278
ngc3406	10.862278	51.023889
ngc3407	10.871608	61.379639
ngc3408	10.869911	58.438139
ngc3409	10.838986	-17.043639
ngc3410	10.864919	51.0065
ngc3412	10.848133	13.412139
ngc3413	10.855761	32.766389
ngc3414	10.854503	27.975111
ngc3415	10.861833	43.712611
ngc3416	10.863419	43.764139
ngc3417	10.850478	8.4735
ngc3418	10.856653	28.112028
ngc3419	10.854928	13.946
ngc3419a	10.855539	14.023444
ngc3420	10.836017	-17.242528
ngc3422	10.854817	-12.402389
ngc3423	10.853981	5.840028
ngc3424	10.862869	32.90075
ngc3426	10.861597	18.480833
ngc3427	10.857314	8.298694
ngc3428,ngc3429	10.858197	9.2795
ngc3430	10.869833	32.950444
ngc3431	10.854178	-17.008028
ngc3432	10.875314	36.618778
ngc3433	10.867742	10.148306
ngc3434	10.866119	3.792056
ngc3435	10.913425	61.289861
ngc3436	10.874303	8.094028
ngc3437	10.876597	22.934139
ngc3438	10.873883	10.54725
ngc3439	10.873811	8.557583
ngc3440	10.897083	57.11875
ngc3441	10.875311	7.224889
ngc3442	10.885586	33.910361
ngc3443	10.883367	17.573639
ngc3444	10.883161	10.210583
ngc3445	10.909858	56.990694
ngc3446	10.868592	-45.13925
ngc3447	10.874111	16.778889
ngc3447a	10.889994	16.772444
ngc3447b	10.891569	16.786
ngc3448	10.910889	54.304861
ngc3449	10.881572	-32.927611
ngc3450	10.801006	-20.849194
ngc3451	10.905803	27.23975
ngc3452	10.903911	-11.405056
ngc3453	10.894583	-21.79275
ngc3454	10.908203	17.344028
ngc3455	10.908636	17.28475
ngc3456	10.900919	-16.027722
ngc3457,ngc3460	10.913508	17.62125
ngc3458	10.933744	57.116972
ngc3459	10.9123	-17.042
ngc3461	10.915358	17.708139
ngc3462	10.922517	7.69675
ngc3463	10.920378	-26.14075
ngc3464	10.911114	-21.066639
ngc3465	10.992019	75.191278
ngc3466	10.937633	9.754444
ngc3467	10.945578	9.758917
ngc3468	10.958658	40.946139
ngc3469	10.949358	-14.300806
ngc3470	10.979139	59.510694
ngc3471	10.985836	61.530694
ngc3472	10.956178	-19.637694
ngc3473	10.968103	17.124417
ngc3474	10.9691	17.095694
ngc3475	10.973672	24.226333
ngc3476,ngc3480	10.968778	9.276139
ngc3477	10.970161	9.217806
ngc3478	10.990933	46.122389
ngc3479,ngc3502	10.982078	-14.961389
ngc3481	10.990603	-7.543639
ngc3482	10.976186	-46.583889
ngc3483	10.983383	-28.476972
ngc3484	10.956681	-19.63325
ngc3485	11.000661	14.841583
ngc3486	11.006631	28.975139
ngc3487	11.012931	17.587611
ngc3488	11.023225	57.677667
ngc3489	11.005158	13.901222
ngc3490	10.998447	9.361889
ngc3491	11.009833	12.161556
ngc3492	11.015833	10.505
ngc3493	11.024397	27.719583
ngc3494	11.019697	3.774306
ngc3495	11.021175	3.627944
ngc3496	10.992725	-60.336861
ngc3498	11.028386	14.350722
ngc3499	11.053064	56.221722
ngc3500	11.030964	75.201361
ngc3501	11.046464	17.989333
ngc3503	11.021456	-59.84575
ngc3504	11.053114	27.9725
ngc3506	11.053603	11.076667
ngc3507	11.057044	18.135444
ngc3509	11.073208	4.828611
ngc3510	11.062047	28.887167
ngc3511	11.056603	-23.086778
ngc3512	11.067483	28.036806
ngc3513	11.0628	-23.2455
ngc3514	11.066639	-18.780583
ngc3515	11.077011	28.227972
ngc3516	11.113192	72.568583
ngc3517	11.093558	56.524917
ngc3519	11.067436	-61.36825
ngc3520	11.119225	-18.023694
ngc3521	11.096828	-0.035861
ngc3522	11.111239	20.085556
ngc3523	11.051756	75.11575
ngc3524	11.108917	11.385417
ngc3526,ngc3531	11.115731	7.173917
ngc3527	11.121719	28.527778
ngc3530	11.14455	57.230194
ngc3532,wishingwellcluster	11.096617	-58.7705
ngc3533	11.118764	-37.172639
ngc3534	11.148794	26.6105
ngc3534b	11.149214	26.596139
ngc3535	11.142756	4.831889
ngc3536	11.147556	28.475694
ngc3537	11.14075	-10.257778
ngc3538	11.192872	75.569722
ngc3539	11.152456	28.672528
ngc3540,ngc3548	11.154467	36.021083
ngc3541	11.142281	-10.491833
ngc3542	11.165408	36.9465
ngc3543	11.182347	61.347028
ngc3544,ngc3571	11.191797	-18.2895
ngc3545	11.170194	36.965556
ngc3545a	11.170069	36.964778
ngc3545b	11.170347	36.966556
ngc3546	11.162997	-13.380861
ngc3547	11.165539	10.720833
ngc3549	11.182464	53.387778
ngc3550	11.177417	28.768333
ngc3551	11.162344	21.758917
ngc3552	11.178569	28.693167
ngc3553	11.177911	28.68475
ngc3554	11.17995	28.660278
ngc3555	11.163981	21.810194
m108,ngc3556	11.191936	55.674111
ngc3557	11.166011	-37.539167
ngc3557b	11.158925	-37.349639
ngc3558	11.182186	28.543806
ngc3559,ngc3560	11.179225	12.016139
ngc3561,theguitar	11.187	28.696472
ngc3562	11.2163	72.879306
ngc3563	11.190139	26.9625
ngc3563a	11.189925	26.961861
ngc3563b	11.190333	26.963583
ngc3564	11.176772	-37.547583
ngc3565,ngc3566	11.129903	-20.021556
ngc3567	11.188522	5.836306
ngc3568	11.180158	-37.447861
ngc3569	11.202247	35.452139
ngc3570	11.200931	27.589778
ngc3572	11.172	-60.248361
ngc3573	11.188492	-36.875528
ngc3574	11.203369	27.624833
ngc3576	11.192131	-61.363
ngc3577	11.229139	48.272722
ngc3578	11.214664	-15.95725
ngc3579	11.199889	-61.243222
ngc3580	11.221092	3.657333
ngc3581	11.200544	-61.301861
ngc3582	11.203325	-61.273556
ngc3583	11.236358	48.318528
ngc3584	11.205497	-61.228611
ngc3585	11.221414	-26.754833
ngc3586	11.208317	-61.35225
m97,ngc3587,owlnebula	11.246586	55.019028
ngc3588	11.234083	20.388611
ngc3589	11.253703	60.699917
ngc3590	11.216381	-60.789028
ngc3591	11.234253	-14.087333
ngc3592	11.240936	17.26
ngc3593	11.243611	12.817667
ngc3594	11.270553	55.704333
ngc3595	11.257097	47.447028
ngc3596	11.251725	14.787028
ngc3597	11.244992	-23.727694
ngc3598	11.253242	17.262694
ngc3599	11.257489	18.110389
ngc3600	11.264447	41.591028
ngc3601	11.25925	5.115417
ngc3602	11.263422	17.416111
ngc3603	11.251831	-61.261222
ngc3604,ngc3611	11.291714	4.555583
ngc3605	11.279608	18.017167
ngc3606	11.271008	-33.827444
ngc3607	11.281844	18.05175
ngc3608	11.283042	18.148694
ngc3609	11.297394	26.625806
ngc3610	11.307019	58.786278
ngc3612	11.304089	26.620556
ngc3613	11.310031	58.0
ngc3614	11.305922	45.748222
ngc3614a	11.303297	45.716889
ngc3615	11.301847	23.397333
ngc3616	11.302464	14.765222
ngc3617	11.297461	-26.134417
ngc3618	11.309039	23.469083
ngc3619	11.322656	57.757833
ngc3620	11.267967	-76.216306
ngc3621	11.304586	-32.814056
ngc3622	11.336769	67.241556
m65,ngc3623	11.315533	13.092361
ngc3624	11.314161	7.521389
ngc3625	11.342039	57.781417
ngc3626,ngc3632	11.334392	18.356833
m66,ngc3627	11.337489	12.991528
ngc3628	11.338047	13.589694
ngc3629	11.342169	26.963361
ngc3630,ngc3645	11.33805	2.964389
ngc3631	11.350797	53.169556
ngc3633	11.340617	3.585611
ngc3634	11.341753	-9.01375
ngc3635	11.342053	-9.013611
ngc3636	11.340289	-10.281778
ngc3637	11.344325	-10.257361
ngc3638	11.336119	-8.105694
ngc3639	11.359911	18.458583
ngc3640	11.351903	3.234833
ngc3641	11.352447	3.194583
ngc3642	11.371636	59.074528
ngc3643	11.356942	3.013917
ngc3646	11.361967	20.169556
ngc3647	11.360717	2.891722
ngc3648	11.375419	39.876889
ngc3650	11.376497	20.703917
ngc3651	11.373972	24.297222
ngc3652	11.377508	37.765111
ngc3653	11.375019	24.279278
ngc3654	11.402983	69.413083
ngc3655	11.381839	16.590028
ngc3656	11.394069	53.842111
ngc3657	11.398772	52.921
ngc3658	11.399517	38.562333
ngc3659	11.395983	17.818667
ngc3660	11.3923	-8.658556
ngc3662	11.396239	-1.104861
ngc3663	11.399975	-12.296444
ngc3664	11.406736	3.325
ngc3664a	11.406972	3.2225
ngc3665	11.412131	38.762861
ngc3666	11.407242	11.342222
ngc3667	11.404728	-13.857306
ngc3667a	11.405969	-13.855806
ngc3668	11.425122	63.446333
ngc3669	11.4241	57.72125
ngc3670	11.413794	23.945222
ngc3671	11.431264	60.479583
ngc3672	11.417353	-9.795389
ngc3673	11.420236	-26.736722
ngc3674	11.440725	57.048389
ngc3675	11.435717	43.585917
ngc3676	11.427083	-11.139667
ngc3677	11.438267	46.974111
ngc3678	11.437711	27.867139
ngc3679	11.36335	-5.757694
ngc3680	11.426967	-43.250111
ngc3681	11.441611	16.863194
ngc3682	11.461444	66.589833
ngc3683	11.458847	56.877056
ngc3683a	11.4866	57.132333
ngc3684	11.453111	17.030167
ngc3685	11.471172	4.327278
ngc3686	11.462214	17.224194
ngc3687	11.466836	29.511056
ngc3688	11.462347	-9.165611
ngc3689	11.469731	25.661167
ngc3690	11.475639	58.561944
ngc3690a	11.475283	58.561306
ngc3690b	11.476008	58.562944
ngc3691	11.469281	16.920472
ngc3692	11.473336	9.407639
ngc3693	11.469881	-13.194861
ngc3694	11.481703	35.414
ngc3695,ngc3698	11.488081	35.575722
ngc3696	11.478858	-11.282833
ngc3697	11.480661	20.795028
ngc3699	11.465875	-59.958056
ngc3700	11.494058	35.514639
ngc3701	11.491367	24.093444
ngc3702	11.503744	-8.862917
ngc3703	11.485933	-8.446444
ngc3705	11.502072	9.276639
ngc3705b	11.495472	9.205806
ngc3706	11.495675	-36.391306
ngc3708	11.510911	-3.222583
ngc3709	11.510908	-3.255917
ngc3710	11.518594	22.768056
ngc3711	11.490422	-11.079083
ngc3712	11.519208	28.567944
ngc3713,ngc3927	11.528339	28.153583
ngc3714	11.531558	28.358472
ngc3715	11.52565	-14.231361
ngc3716	11.528092	3.488
ngc3717	11.525553	-30.30775
ngc3718	11.543014	53.067917
ngc3719	11.537072	0.819278
ngc3720	11.539333	0.804
ngc3721	11.568839	-9.467139
ngc3722	11.573142	-9.680056
ngc3723	11.541819	-9.969528
ngc3724	11.574633	-9.660194
ngc3725	11.561258	61.888
ngc3726	11.555867	47.029194
ngc3727	11.561369	-13.878889
ngc3728	11.554383	24.446889
ngc3729	11.5637	53.125556
ngc3730	11.571356	-9.576111
ngc3731	11.569911	12.512306
ngc3732	11.570539	-9.845667
ngc3733	11.583778	54.8505
ngc3734	11.577967	-14.081833
ngc3735	11.59925	70.535583
ngc3736	11.594925	73.451833
ngc3737	11.593439	54.948556
ngc3738	11.596886	54.523889
ngc3739	11.593778	25.088639
ngc3740	11.603411	59.9765
ngc3741	11.601717	45.283639
ngc3742	11.592364	-37.956389
ngc3743	11.599267	21.722611
ngc3744	11.599408	23.011556
ngc3745	11.629008	22.021278
ngc3746	11.628783	22.009833
ngc3747	11.541961	74.378389
ngc3748	11.630294	22.026139
ngc3749	11.598114	-37.997361
ngc3750	11.631011	21.97425
ngc3751	11.631628	21.936472
ngc3752	11.542281	74.627528
ngc3753	11.631639	21.981389
ngc3754	11.631922	21.9855
ngc3755	11.609269	36.410333
ngc3756	11.613339	54.293556
ngc3757	11.617461	58.415528
ngc3758	11.608083	21.596111
ngc3759	11.615025	54.823306
ngc3759a	11.616119	55.162056
ngc3761	11.612256	22.992028
ngc3762	11.623286	61.759361
ngc3764	11.615028	17.889444
ngc3765	11.617828	24.09625
ngc3766,pearlcluster	11.603997	-61.605167
ngc3767	11.620989	16.877167
ngc3768	11.620689	17.839889
ngc3769	11.628919	47.893083
ngc3769a	11.630933	47.881333
ngc3770	11.632983	59.616917
ngc3771	11.651667	-9.348194
ngc3772	11.630133	22.691278
ngc3773	11.636911	12.112056
ngc3774	11.641739	-8.976139
ngc3775	11.64075	-10.638778
ngc3776	11.638328	-3.354389
ngc3777	11.601903	-12.569083
ngc3778	11.639281	-50.715361
ngc3780	11.656211	56.270667
ngc3781	11.651044	26.36175
ngc3782	11.655767	46.513833
ngc3783	11.650489	-37.738667
ngc3784	11.658278	26.309139
ngc3785	11.659136	26.302278
ngc3786	11.661819	31.909278
ngc3787	11.660542	20.454694
ngc3788	11.662403	31.931194
ngc3789	11.63585	-9.607139
ngc3790	11.663128	17.71225
ngc3791	11.661583	-9.36725
ngc3792	11.660703	5.0995
ngc3793	11.667219	31.877722
ngc3794,ngc3804	11.681506	56.202028
ngc3795	11.668519	58.613083
ngc3795a	11.655919	58.268694
ngc3796	11.675311	60.298917
ngc3797	11.670364	31.906556
ngc3798	11.670539	24.697056
ngc3799	11.669272	15.327306
ngc3800	11.670419	15.342361
ngc3801	11.671372	17.728056
ngc3802	11.671883	17.765333
ngc3803	11.671458	17.80125
ngc3805	11.678244	20.342944
ngc3806	11.679619	17.796278
ngc3807	11.698522	17.818917
ngc3808	11.679	22.437778
ngc3808a	11.678956	22.429361
ngc3808b	11.679067	22.446944
ngc3809	11.687794	59.885778
ngc3810	11.682989	11.471139
ngc3811	11.687953	47.690806
ngc3812	11.685475	24.821694
ngc3813	11.688517	36.546806
ngc3814	11.691022	24.805417
ngc3815	11.694247	24.8005
ngc3816	11.696678	20.103639
ngc3817	11.698042	10.304389
ngc3818	11.699267	-6.155667
ngc3819	11.701628	10.351139
ngc3820	11.701364	10.38425
ngc3821	11.702531	20.315667
ngc3822,ngc3848	11.703086	10.277778
ngc3823	11.704194	-13.866944
ngc3824	11.712461	52.779583
ngc3825,ngc3852	11.706592	10.264139
ngc3826,ngc3830	11.709125	26.488889
ngc3827	11.710075	18.845444
ngc3828	11.716228	16.487611
ngc3829	11.724244	52.711139
ngc3831	11.721833	-12.878361
ngc3832	11.7254	22.725444
ngc3833	11.724717	10.161861
ngc3834	11.727147	19.090472
ngc3835	11.734694	60.119778
ngc3835a	11.789694	60.300444
ngc3836	11.724944	-16.795556
ngc3837	11.732342	19.894583
ngc3838	11.737156	57.948222
ngc3839	11.731758	10.784694
ngc3840	11.733044	20.077028
ngc3841	11.733931	19.971889
ngc3842	11.733931	19.949806
ngc3843	11.731842	7.925694
ngc3844	11.733553	20.029333
ngc3845	11.734853	19.996111
ngc3846	11.741411	55.65225
ngc3846a	11.73745	55.034972
ngc3847,ngc3856	11.737214	33.514528
ngc3850	11.759878	55.886889
ngc3851	11.739006	19.980861
ngc3853	11.741203	16.558111
ngc3854,ngc3865	11.747792	-9.233278
ngc3857	11.747264	19.532861
ngc3858,ngc3866	11.753244	-9.313972
ngc3859	11.747844	19.454194
ngc3860	11.746989	19.795028
ngc3861	11.751078	19.973694
ngc3862	11.751392	19.606306
ngc3863	11.751533	8.4695
ngc3864	11.754356	19.392111
ngc3867	11.758228	19.400167
ngc3868	11.758317	19.444694
ngc3869	11.762656	10.824611
ngc3870	11.765722	50.19975
ngc3872	11.763628	13.766694
ngc3873	11.762806	19.773944
ngc3874	11.760486	8.573917
ngc3875	11.763736	19.767417
ngc3876	11.757408	9.160722
ngc3877	11.768806	47.494333
ngc3878	11.771606	33.204472
ngc3879	11.780394	69.383694
ngc3880	11.772842	33.161778
ngc3881	11.776225	33.106417
ngc3882	11.768486	-56.388139
ngc3883	11.779772	20.675417
ngc3884	11.77005	20.391639
ngc3885	11.779581	-27.922167
ngc3886	11.784889	19.837194
ngc3887	11.784603	-16.854611
ngc3888	11.792881	55.967222
ngc3889	11.796703	56.018333
ngc3890,ngc3939	11.822181	74.302194
ngc3891	11.800933	30.359333
ngc3892	11.800275	-10.962056
ngc3893	11.810608	48.710833
ngc3894	11.813989	59.415667
ngc3895	11.817786	59.432667
ngc3896	11.815664	48.674667
ngc3897	11.816517	35.016056
ngc3898	11.820936	56.084361
ngc3899,ngc3912	11.834569	26.47925
ngc3900	11.819294	27.022028
ngc3901	11.713811	77.372694
ngc3902	11.821878	26.121611
ngc3903	11.81765	-37.517111
ngc3904	11.820339	-29.27675
ngc3905	11.818031	-9.729833
ngc3906	11.827917	48.425972
ngc3907	11.825039	-1.086528
ngc3907b	11.823206	-1.083778
ngc3908	11.8313	12.185917
ngc3909	11.835594	-48.238139
ngc3910	11.833142	21.333639
ngc3911	11.822803	24.938472
ngc3914	11.842403	6.567583
ngc3916	11.847514	55.143639
ngc3917	11.845953	51.824667
blueplanetary,ngc3918	11.838319	-57.182333
ngc3919	11.844869	20.015194
ngc3920	11.834981	24.92
ngc3921	11.851908	55.07875
ngc3922,ngc3924	11.853731	50.156889
ngc3923	11.850469	-28.806028
ngc3925	11.855825	21.889139
ngc3926	11.857611	22.026944
ngc3926a	11.857378	22.027972
ngc3926b	11.857842	22.025972
miniaturespiral,ngc3928	11.863228	48.683139
ngc3929	11.861814	21.002722
ngc3930	11.862781	38.015111
ngc3931	11.853736	52.000861
ngc3932	11.869678	48.620389
ngc3933	11.867236	16.809694
ngc3934	11.870156	16.851444
ngc3935	11.873353	32.403806
ngc3936	11.872386	-26.905889
ngc3937	11.878506	20.631306
ngc3938	11.880403	44.120722
ngc3940	11.879569	20.989278
ngc3941	11.882044	36.986333
ngc3942	11.858372	-11.424722
ngc3943	11.882381	20.479111
ngc3944	11.884744	26.206944
ngc3945	11.887147	60.675556
ngc3946	11.889064	21.021528
ngc3947	11.888978	20.751722
ngc3948	11.893514	20.950778
ngc3949	11.894922	47.858694
ngc3950	11.894836	47.884583
ngc3951	11.894792	23.382222
ngc3953	11.896922	52.326778
ngc3954	11.894911	20.8825
ngc3955	11.899208	-23.164167
ngc3956	11.900192	-20.567333
ngc3958	11.909356	58.367028
ngc3959	11.910458	-7.7565
ngc3960	11.842558	-55.669833
ngc3961	11.916011	69.330111
ngc3962	11.911139	-13.975028
ngc3963	11.916308	58.493639
ngc3964	11.914856	28.262417
ngc3965	11.906419	-10.866861
ngc3966,ngc3986	11.945608	32.021778
ngc3967	11.919556	-7.843778
ngc3968	11.924639	11.968361
ngc3969	11.919233	-18.927417
ngc3970	11.924464	-12.061278
ngc3971,ngc3984	11.926775	29.995917
ngc3972	11.929192	55.32075
ngc3973	11.926944	11.997389
ngc3974	11.927817	-12.027444
ngc3975	11.931581	60.529417
ngc3976	11.932581	6.749444
ngc3977,ngc3980	11.935333	55.390778
ngc3978	11.9362	60.522528
ngc3981	11.935403	-19.896167
ngc3982	11.941147	55.12525
ngc3983	11.939911	23.867944
ngc3985	11.945031	48.333944
ngc3987	11.955811	25.195389
ngc3988	11.956728	27.877528
ngc3989	11.957414	25.233083
ngc3990	11.959878	55.458667
ngc3991	11.958633	32.337778
m109,ngc3992	11.959994	53.374528
ngc3993	11.960506	25.240611
ngc3994	11.960242	32.277611
ngc3995	11.96225	32.294056
ngc3996	11.962794	14.297417
ngc3997	11.963397	25.270639
ngc3998	11.965592	55.453583
ngc3999	11.965692	25.068278
ngc4000	11.965839	25.144472
ngc4001	11.96855	47.334861
ngc4002	11.966472	23.202056
ngc4003	11.9664	23.124889
ngc4004	11.968119	27.878861
ngc4005,ngc4007	11.969492	25.12225
ngc4006	11.968272	-2.120083
ngc4008	11.9714	28.1925
ngc4009	11.970847	25.18975
ngc4010	11.977192	47.2615
ngc4011	11.973731	25.097639
ngc4012	11.974314	10.0215
ngc4013	11.975383	43.946583
ngc4014,ngc4028	11.976614	16.177306
ngc4015	11.978583	25.040278
ngc4016	11.974728	27.528778
ngc4017	11.979353	27.452444
ngc4018	11.977972	25.316417
ngc4020	11.982408	30.411889
ngc4021	11.984053	25.083222
ngc4022	11.983614	25.222806
ngc4023	11.984853	24.988972
ngc4024	11.975347	-18.346833
ngc4025	11.986164	37.793417
ngc4026	11.990331	50.961694
ngc4027	11.991714	-19.265222
ngc4027a	11.991497	-19.332
ngc4029	12.000881	8.181722
ngc4030	12.006564	-1.100083
ngc4031	12.008708	31.947583
ngc4032	12.009117	20.073944
ngc4033	12.00965	-17.842611
ngc4034	12.024906	69.323917
ngc4035	12.00815	-15.948083
ngc4036	12.024097	61.895778
ngc4037	12.023242	13.401028
antennaegalaxies,ngc4038	12.031392	-18.867611
ngc4039	12.031531	-18.886194
ngc4040	12.034844	17.823222
ngc4041	12.036722	62.137222
ngc4042	12.046328	20.16325
ngc4043	12.039711	4.329806
ngc4044	12.041531	-0.212417
ngc4045,ngc4046	12.045067	1.976806
ngc4045a	12.045192	1.952222
ngc4047	12.047411	48.636194
ngc4048	12.047275	18.015583
ngc4049	12.048528	18.7525
ngc4050	12.048319	-16.373611
ngc4051	12.052669	44.531333
ngc4052	12.034775	-63.223472
ngc4053	12.053214	19.728833
ngc4054	12.053639	57.894444
ngc4055,ngc4061	12.067078	20.232333
ngc4056	12.066047	20.3125
ngc4057,ngc4065	12.068381	20.235083
ngc4058	12.063628	3.548222
ngc4059,ngc4070	12.069806	20.409833
ngc4060	12.066944	20.337417
ngc4062	12.067731	31.895806
ngc4063	12.068331	1.846972
ngc4064	12.069767	18.443417
ngc4066	12.069283	20.347944
ngc4067	12.069872	10.854389
ngc4069	12.068344	20.323778
ngc4071	12.071047	-67.310111
ngc4072	12.070511	20.209722
ngc4073	12.074186	1.895972
ngc4074	12.074911	20.316222
ngc4075	12.077175	2.072528
ngc4076	12.0757	20.204944
ngc4077,ngc4140	12.077236	1.787722
ngc4078,ngc4107	12.0799	10.595583
ngc4079	12.080514	-2.382389
ngc4080	12.081064	26.992528
ngc4081	12.076086	64.43675
ngc4082	12.086514	10.670611
ngc4083	12.087236	10.613222
ngc4084	12.087572	21.214444
ngc4085	12.089642	50.352944
ngc4086	12.091492	20.24675
ngc4087	12.093147	-26.522639
ngc4088	12.092831	50.539028
ngc4089	12.093731	20.555722
ngc4090	12.091089	20.30875
ngc4091	12.094469	20.555722
ngc4092	12.097253	20.477
ngc4093	12.097631	20.521972
ngc4094	12.098322	-14.526417
ngc4095	12.098394	20.572528
ngc4096	12.100314	47.478444
ngc4097	12.100697	36.863667
ngc4098,ngc4099	12.101083	20.606111
ngc4100	12.102347	49.582694
ngc4101	12.102936	25.557
ngc4102	12.106386	52.711083
ngc4103	12.110992	-61.250083
ngc4104	12.110825	28.174194
ngc4105	12.111325	-29.760222
ngc4106	12.112444	-29.768306
ngc4108	12.112381	67.163083
ngc4108a	12.097128	67.252083
ngc4108b	12.119894	67.235167
ngc4109	12.1142	42.995639
ngc4110	12.117625	18.531722
ngc4111	12.117536	43.065722
ngc4112	12.119297	-40.208167
ngc4113,ngc4122	12.119022	32.995889
ngc4114	12.120081	-14.185472
ngc4115	12.119319	14.406556
ngc4116	12.126986	2.6905
ngc4117	12.129475	43.126361
ngc4118	12.131353	43.111056
ngc4120	12.14195	69.544833
ngc4121	12.132397	65.113944
ngc4123	12.136419	2.878278
ngc4125	12.135006	65.174139
ngc4126	12.143733	16.142778
ngc4127	12.140656	76.804028
ngc4128	12.142314	68.767611
ngc4129,ngc4130	12.148117	-9.0365
ngc4131	12.146469	29.304778
ngc4132	12.150389	29.250111
ngc4133	12.147211	74.904306
ngc4134	12.152781	29.176917
ngc4135	12.152447	44.003194
ngc4136	12.154914	29.927611
ngc4137	12.154864	44.090167
ngc4138	12.158272	43.685306
ngc4141	12.163144	58.849194
ngc4142	12.158386	53.104944
ngc4143	12.160017	42.534167
ngc4144	12.166278	46.457167
ngc4145	12.167089	39.883861
ngc4146	12.171739	26.43075
ngc4147,ngc4153	12.168381	18.542139
ngc4148	12.168881	35.877611
ngc4149,ngc4154	12.175789	58.304139
ngc4150	12.176014	30.401528
ngc4151	12.175717	39.405722
ngc4152	12.177083	16.032917
ngc4155	12.179358	19.040833
ngc4156	12.180447	39.472722
ngc4157	12.184547	50.484667
ngc4158	12.186158	20.175667
ngc4159	12.181561	76.125861
ngc4160	12.200483	43.735583
ngc4161	12.192628	57.7375
ngc4162	12.197908	24.123667
ngc4163,ngc4167	12.202544	36.169194
ngc4164	12.201517	13.205639
ngc4166	12.202656	17.757028
ngc4168	12.204797	13.205194
ngc4169	12.205217	29.179417
ngc4170	12.203678	29.166806
ngc4171	12.210664	29.2245
ngc4172	12.204136	56.177556
ngc4173	12.205961	29.207056
ngc4174	12.207469	29.149222
ngc4175	12.208625	29.168444
ngc4176	12.210231	-9.160472
ngc4177	12.211461	-14.014556
ngc4179	12.214475	1.299694
ngc4180,ngc4182	12.217514	7.038944
ngc4181	12.213608	52.903306
ngc4183	12.221356	43.698583
ngc4184	12.225719	-62.721417
ngc4185	12.222833	28.510972
ngc4186	12.235147	14.725806
ngc4187	12.2248	50.7415
ngc4188	12.235378	-12.586
ngc4190	12.229103	36.634028
ngc4191	12.230667	7.200889
m98,ngc4192	12.230081	14.900333
medusagalaxymerger,ngc4194	12.235964	54.526833
ngc4195	12.238356	59.615444
ngc4196	12.241597	28.423444
ngc4197	12.244042	5.805722
ngc4199	12.247278	59.9075
ngc4199a	12.246842	59.906194
ngc4199b	12.247694	59.908389
ngc4200	12.245619	12.18075
ngc4201	12.244961	-11.582861
ngc4202	12.302375	-1.064111
ngc4203	12.251406	33.197333
ngc4204	12.254011	20.658583
ngc4205	12.248761	63.782778
ngc4207	12.258472	9.584889
ngc4208,ngc4212	12.260933	13.9015
ngc4209	12.257172	28.468417
ngc4210	12.254397	65.985333
ngc4211	12.259958	28.177639
ngc4211a	12.260367	28.169639
ngc4213	12.260433	23.981889
ngc4214,ngc4228	12.260881	36.326889
ngc4215	12.26515	6.401139
ngc4216	12.265122	13.149389
ngc4217	12.264139	47.091778
ngc4218	12.262892	48.130833
ngc4219	12.274256	-43.32425
ngc4219a	12.299969	-43.540028
ngc4220	12.269919	47.88325
ngc4221	12.266628	66.230806
ngc4222	12.272922	13.307056
ngc4224	12.276053	7.462083
ngc4225	12.277325	-12.327667
ngc4226	12.273967	47.025194
ngc4227	12.276028	33.522056
ngc4229	12.277442	33.560889
ngc4230	12.285936	-55.286139
ngc4231	12.280242	47.457389
ngc4232	12.280286	47.438806
ngc4233	12.285467	7.624389
ngc4234	12.285878	3.683056
ngc4236	12.278367	69.462583
ngc4237	12.286506	15.323972
ngc4238	12.282167	63.409917
ngc4239	12.287481	16.531389
ngc4240,ngc4243	12.2901	-9.951639
ngc4242	12.291717	45.619306
ngc4244	12.291572	37.807111
ngc4245	12.293547	29.608
ngc4247	12.299467	7.273944
ngc4248	12.297181	47.409194
ngc4249	12.299831	5.598583
ngc4250	12.290631	70.802583
ngc4251	12.302292	28.175389
ngc4252	12.308581	5.559472
ngc4253	12.307364	29.812861
comapinwheel,m99,ngc4254,virgoclusterpinwheel	12.313778	14.4165
ngc4255	12.315597	4.786139
ngc4256	12.311969	65.89825
ngc4257	12.318464	5.725972
m106,ngc4258	12.315972	47.303972
ngc4259	12.322836	5.376389
ngc4260	12.322844	6.098667
ngc4261	12.323117	5.825222
ngc4262	12.325158	14.877667
ngc4263,ngc4265	12.328389	-12.225556
ngc4264	12.3266	5.84675
ngc4266	12.328417	5.538278
ngc4267	12.329233	12.798278
ngc4268	12.329783	5.283778
ngc4269	12.330331	6.014972
ngc4270	12.330408	5.463444
ngc4271	12.325722	56.736583
ngc4272	12.3299	30.339083
ngc4273	12.332244	5.343333
ngc4274	12.330719	29.614472
ngc4275	12.331272	27.621
ngc4276	12.335411	7.691861
ngc4277	12.334367	5.341361
ngc4278	12.335228	29.28075
ngc4279	12.340278	-11.666611
ngc4280	12.342194	-11.652444
ngc4281	12.339311	5.386389
ngc4282	12.340086	5.572833
ngc4283	12.339125	29.310944
ngc4284	12.336839	58.092889
ngc4285	12.344389	-11.641917
ngc4287	12.346806	5.639889
ngc4288	12.343919	46.291667
ngc4288a	12.344603	46.255444
ngc4289	12.350625	3.722139
ngc4290	12.346536	58.0925
ngc4291	12.338389	75.370833
ngc4292	12.354572	4.595694
ngc4293	12.353581	18.382389
ngc4294	12.354953	11.510444
ngc4295	12.352717	28.165111
ngc4296	12.357886	6.653556
ngc4297	12.357614	6.671028
ngc4298	12.3591	14.606167
ngc4299	12.361264	11.499917
ngc4300	12.361519	5.384806
ngc4301,ngc4303a	12.374225	4.566278
ngc4302	12.3618	14.598306
m61,ngc4303	12.36525	4.473639
ngc4304	12.3702	-33.4845
ngc4305	12.367667	12.740917
ngc4306	12.367808	12.787472
ngc4307	12.368244	9.043639
ngc4308	12.365792	30.074361
ngc4309	12.370106	7.144306
ngc4310,ngc4338	12.373972	29.209028
ngc4311	12.374125	29.145944
ngc4312	12.375378	15.537917
ngc4313	12.377372	11.800944
ngc4314	12.375506	29.895889
ngc4315	12.379206	9.305389
ngc4316	12.3784	9.332472
ngc4317	12.378328	31.037861
ngc4318	12.378692	8.198278
ngc4319,ngc4345	12.362186	75.322583
ngc4320	12.3827	10.548333
m100,ngc4321	12.381897	15.821806
ngc4322	12.378303	15.903278
ngc4323	12.383814	15.905583
ngc4324	12.38505	5.250333
ngc4325,ngc4368	12.385189	10.621194
ngc4326	12.386564	6.072139
ngc4327	12.385419	15.7365
ngc4328	12.388897	15.820389
ngc4329	12.389086	-12.558611
ngc4330	12.388125	11.367972
ngc4331	12.376656	76.172472
ngc4332	12.379656	65.843778
ngc4333	12.389519	6.040722
ngc4334	12.389967	7.473194
ngc4335	12.383856	58.444556
ngc4337	12.400919	-58.123778
ngc4339	12.393042	6.08175
ngc4340	12.393136	16.722361
ngc4343	12.394083	6.954083
ngc4344	12.393742	17.540861
ngc4346	12.391094	46.993833
ngc4347	12.3979	-3.240417
ngc4348	12.398331	-3.442917
ngc4349	12.401678	-61.870444
ngc4350	12.399408	16.693417
ngc4351,ngc4354	12.400417	12.204778
ngc4352	12.401394	11.218056
ngc4355,ngc4418	12.448506	-0.877611
ngc4357,ngc4381	12.399672	48.779472
ngc4358	12.400561	58.385222
ngc4359	12.403103	31.521944
ngc4360	12.406028	9.292778
ngc4361	12.408544	-18.784833
ngc4362,ngc4364	12.403128	58.360667
ngc4363	12.391222	74.952222
ngc4365	12.407856	7.317667
ngc4366	12.413058	7.353028
ngc4367	12.409761	12.182306
ngc4369	12.410056	39.383
ngc4370	12.41525	7.444889
ngc4371	12.415397	11.704222
ngc4372	12.429272	-72.659083
ngc4373	12.421617	-39.759722
ngc4373a	12.427147	-39.319667
ngc4373b	12.445494	-39.134222
m84,ngc4374	12.417706	12.886972
ngc4375	12.416797	28.558611
ngc4376	12.421683	5.741194
ngc4377	12.420094	14.762167
ngc4378	12.421694	4.925139
ngc4379	12.420761	15.607472
ngc4380	12.422825	10.016806
m85,ngc4382	12.423364	18.1915
ngc4383	12.423756	16.470139
ngc4384	12.419994	54.506222
ngc4385	12.428556	0.572611
ngc4386	12.407875	75.528917
ngc4387	12.428244	12.810528
ngc4388	12.429653	12.662083
ngc4389	12.426417	45.684667
ngc4391	12.421886	64.933472
ngc4392	12.421933	45.847472
ngc4393	12.430897	27.561556
ngc4394	12.432092	18.214056
ngc4395	12.430239	33.546917
ngc4396	12.433006	15.671472
ngc4397	12.432822	18.301028
ngc4398	12.435397	10.686083
ngc4399	12.428614	33.516083
ngc4400	12.432197	33.514833
ngc4401	12.432658	33.528361
ngc4402	12.435458	13.113333
ngc4403	12.436886	-7.684944
ngc4404	12.437836	-7.680833
m86,ngc4406	12.436594	12.946222
ngc4407,ngc4413	12.442292	12.610972
ngc4408	12.438122	27.871167
ngc4409,ngc4420	12.449583	2.494361
ngc4410	12.44135	9.019667
ngc4410a	12.441192	9.019861
ngc4410b	12.44155	9.019222
ngc4411b	12.446453	8.884611
ngc4412	12.443356	3.964694
ngc4414	12.440861	31.223528
ngc4415	12.444581	8.435694
ngc4416	12.446311	7.919
ngc4417	12.447392	9.58425
ngc4419	12.449011	15.047389
ngc4421	12.450706	15.461472
ngc4422	12.453364	-5.831
ngc4423	12.452492	5.880167
ngc4424	12.453225	9.420667
ngc4425	12.453703	12.734722
ngc4426,ngc4427	12.452925	27.838194
ngc4428	12.457861	-8.167889
ngc4429	12.457364	11.107722
ngc4430	12.457336	6.262778
ngc4431	12.457606	12.290278
ngc4432	12.459158	6.23325
ngc4433	12.460719	-8.278417
ngc4434	12.460189	8.154333
eyes,ngc4435	12.461247	13.078944
ngc4436	12.461456	12.315889
ngc4437,ngc4517	12.545997	0.115028
ngc4438	12.462664	13.008833
ngc4439	12.473986	-60.103222
ngc4440	12.464881	12.293278
ngc4441	12.455653	64.8015
ngc4442	12.467744	9.803722
ngc4443,ngc4461	12.484169	13.18375
ngc4444	12.476781	-43.26175
ngc4446	12.468553	13.91175
ngc4447	12.470147	13.899222
ngc4448	12.470953	28.620306
ngc4449	12.46975	44.093639
ngc4450	12.474897	17.084944
ngc4451	12.477931	9.258806
ngc4452	12.478697	11.755028
ngc4453	12.479778	6.5075
ngc4454	12.480764	-1.939194
ngc4455	12.478919	22.820444
ngc4456	12.464556	-30.097889
ngc4457	12.483058	3.570583
ngc4458	12.482658	13.241889
ngc4459	12.483336	13.978361
ngc4460	12.479322	44.864222
ngc4462	12.489228	-23.166361
ngc4463	12.498672	-64.789667
ngc4464	12.489247	8.156611
ngc4465	12.489872	8.026
ngc4466	12.491825	7.696417
ngc4467	12.491736	7.992861
ngc4468	12.491917	14.049083
ngc4469	12.491119	8.749917
ngc4470,ngc4610	12.493828	7.824194
ngc4471	12.493625	7.93275
m49,ngc4472	12.496322	8.000472
ngc4473	12.496908	13.429361
ngc4474	12.498208	14.068583
ngc4475	12.49655	27.243333
ngc4476	12.499744	12.348667
ngc4477	12.500611	13.636611
ngc4478	12.504839	12.328556
ngc4479	12.505103	13.577639
ngc4480	12.507439	4.246583
ngc4481	12.496853	64.033
ngc4483	12.511292	9.015667
ngc4484	12.4813	-11.652056
ngc4485	12.508647	41.701167
m87,ngc4486,virgogalaxy	12.513728	12.391111
ngc4486a	12.516031	12.270361
ngc4486b	12.508881	12.490167
ngc4487	12.517906	-8.053917
ngc4488	12.514269	8.36
ngc4489	12.514514	16.758861
ngc4490	12.510067	41.643889
ngc4491	12.515864	11.483528
ngc4493	12.518992	0.613694
ngc4494	12.523361	25.77525
ngc4495	12.523022	29.136472
ngc4496	12.527778	3.932778
ngc4496a,ngc4505	12.527558	3.939472
ngc4496b	12.528022	3.926333
ngc4498	12.527656	16.852778
ngc4499	12.534706	-39.982472
ngc4500	12.522822	57.964639
m88,ngc4501	12.5331	14.420389
ngc4502	12.534264	16.687722
ngc4503	12.535064	11.176417
ngc4504	12.538181	-7.563444
ngc4506	12.536258	13.419611
ngc4507	12.593508	-39.90925
ngc4508	12.538172	5.819972
ngc4509	12.551886	32.091556
ngc4510	12.529781	64.233806
ngc4511	12.535586	56.471167
ngc4512,ngc4521	12.546569	63.939194
ngc4513	12.533756	66.332583
ngc4514	12.545269	29.712389
ngc4515	12.551381	16.265528
ngc4516	12.552094	14.574944
ngc4517a	12.541153	0.389667
ngc4518	12.553267	7.851639
ngc4519	12.558403	8.65475
ngc4519a	12.556864	8.69075
ngc4522	12.561031	9.175028
ngc4523	12.563333	15.168306
ngc4524	12.565108	-12.027611
ngc4525	12.564206	30.277472
ngc4526,ngc4560	12.567525	7.699528
ngc4527	12.569006	2.653667
ngc4528	12.568353	11.32125
ngc4529	12.547681	20.1835
ngc4530	12.563253	41.353472
ngc4531	12.571081	13.075333
ngc4532	12.572036	6.467694
ngc4533	12.572783	2.325361
ngc4534	12.568172	35.518333
ngc4535	12.572308	8.19775
ngc4536	12.574181	2.188139
ngc4537,ngc4542	12.580253	50.805167
ngc4538	12.578028	3.323667
ngc4539	12.576317	18.202694
ngc4540	12.580797	15.551722
ngc4541	12.586294	-0.221139
ngc4543	12.588956	6.115083
ngc4544	12.593492	3.034528
ngc4545	12.576153	63.525056
ngc4546	12.591531	-3.793194
ngc4547	12.581067	58.916778
m91,ngc4548	12.590681	14.496333
ngc4549	12.589242	58.949667
ngc4550	12.591828	12.220833
ngc4551	12.593875	12.263972
m89,ngc4552	12.594392	12.556333
ngc4553	12.602111	-39.438667
ngc4554	12.599867	11.265361
ngc4556	12.596072	26.908889
ngc4557	12.59715	27.053778
ngc4558	12.597958	26.992139
ngc4559	12.599347	27.96
ngc4562,ngc4565a	12.593	25.85
ngc4563	12.603578	26.941444
ngc4564	12.607494	11.439278
needlegalaxy,ngc4565	12.605772	25.987667
ngc4566	12.600031	54.220972
butterflygalaxies,ngc4567,siamesetwins	12.609086	11.258
ngc4568	12.609517	11.238889
m90,ngc4569	12.613831	13.162944
ngc4570	12.614833	7.246639
ngc4572	12.595917	74.245556
ngc4573	12.628831	-43.621139
ngc4574	12.628753	-35.517639
ngc4575	12.630867	-40.537361
ngc4576	12.625989	4.367694
ngc4577,ngc4591	12.653456	6.012306
ngc4578	12.625156	9.555083
m58,ngc4579	12.628756	11.818194
ngc4580	12.630108	5.368528
ngc4581	12.634769	1.47775
ngc4582	12.636167	0.18275
ngc4583	12.634594	33.458833
ngc4584	12.638297	13.109889
ngc4585	12.637022	28.937028
ngc4586	12.641222	4.319083
ngc4587	12.643172	2.657333
ngc4588	12.645953	6.768167
ngc4589	12.623608	74.191917
m68,ngc4590	12.657781	-26.743028
ngc4592	12.655206	-0.532
ngc4593	12.660953	-5.34425
m104,ngc4594,sombrerogalaxy	12.666508	-11.623056
ngc4595	12.664419	15.297806
ngc4596	12.665542	10.176139
ngc4597	12.670258	-5.799278
ngc4598	12.669981	8.38375
ngc4599	12.674192	1.196917
ngc4600	12.673044	3.11775
ngc4601	12.67965	-40.893056
ngc4602	12.676903	-5.133
ngc4603	12.682003	-40.976389
ngc4603a	12.660256	-40.740028
ngc4603b	12.674928	-41.069833
ngc4603c	12.678642	-40.763361
ngc4603d	12.70225	-40.820861
ngc4604	12.679183	-5.302889
ngc4605	12.666494	61.609194
ngc4606	12.68265	11.912222
ngc4607	12.686778	11.886639
ngc4608	12.687025	10.155667
coalsackcluster,ngc4609	12.704675	-62.99575
ngc4612	12.692431	7.314889
ngc4613	12.691375	26.088611
ngc4614	12.692075	26.042667
ngc4615	12.6937	26.072833
ngc4616	12.704569	-40.642056
ngc4617	12.684964	50.393417
ngc4619	12.695708	35.062778
ngc4620	12.699822	12.942778
m59,ngc4621	12.700622	11.647028
ngc4622	12.71045	-40.744222
ngc4622a	12.730308	-40.714611
ngc4622b	12.730725	-40.717472
ngc4623	12.702969	7.676944
ngc4624,ngc4664,ngc4665	12.751664	3.055778
ngc4626	12.707031	-7.044278
ngc4627	12.699911	32.573556
ngc4628	12.707017	-6.971
ngc4629	12.709075	-1.350667
ngc4630	12.708647	3.96025
ngc4631,whalegalaxy	12.702225	32.5415
ngc4632	12.708897	-0.082611
ngc4634	12.711378	14.295833
ngc4635	12.7109	19.945306
ngc4636	12.713842	2.687778
ngc4637	12.715028	11.438278
ngc4638,ngc4667	12.713172	11.4425
ngc4639	12.714553	13.257389
ngc4640	12.716047	12.286972
ngc4641	12.718794	12.051194
ngc4642	12.721606	-0.64425
ngc4643	12.722261	1.978278
ngc4644	12.71185	55.1455
ngc4645	12.736108	-41.749944
ngc4645a	12.718214	-41.358917
ngc4645b	12.725328	-41.362528
ngc4646	12.714478	54.856
ngc4647	12.725642	11.581861
ngc4648	12.695664	74.420944
m60,ngc4649	12.727772	11.552694
ngc4650	12.738775	-40.731806
ngc4650a	12.746961	-40.714306
ngc4651,umbrellagalaxy	12.728508	16.393389
ngc4652	12.722153	58.964889
ngc4653	12.730808	-0.561222
ngc4654	12.732383	13.126667
ngc4655	12.726803	41.018528
ngc4656	12.732703	32.168139
ngc4657	12.735306	32.20875
ngc4658	12.743831	-10.083111
ngc4659	12.741497	13.498556
ngc4660	12.742217	11.190528
ngc4661	12.754153	-40.82425
ngc4662	12.740611	37.121222
ngc4666	12.752386	-0.461889
ngc4668	12.758886	-0.535722
ngc4669	12.746317	54.875667
ngc4670	12.754742	27.125417
ngc4671	12.763231	-7.069694
ngc4672	12.771042	-41.705972
ngc4673	12.759631	27.060833
ngc4674	12.767631	-8.655444
ngc4675	12.758858	54.737611
micegalaxy,ngc4676	12.769639	30.727222
ngc4677	12.782536	-41.582528
ngc4679	12.791736	-39.570861
ngc4680	12.781864	-11.637056
ngc4681	12.791336	-43.334806
ngc4682	12.787636	-10.063444
ngc4683	12.795103	-41.528278
ngc4684	12.7882	-2.727417
ngc4685	12.786511	19.464361
ngc4686	12.777744	54.534278
ngc4687	12.789936	35.352056
ngc4688	12.796256	4.336056
ngc4689	12.795989	13.762806
ngc4690	12.798756	-1.656056
ngc4691	12.803786	-3.332722
ngc4692	12.7987	27.222361
ngc4693	12.785881	71.176139
ngc4694	12.804189	10.983611
ngc4696	12.813681	-41.310833
ngc4696a	12.782117	-41.49675
ngc4696b	12.789383	-41.2375
ngc4696c	12.800739	-40.818556
ngc4696d	12.806017	-41.714028
ngc4696e	12.807256	-40.9365
ngc4697	12.809967	-5.80075
ngc4698	12.806364	8.487389
ngc4699	12.817286	-8.664861
ngc4700	12.818931	-11.409861
ngc4701	12.819886	3.388722
ngc4702	12.817081	27.179139
ngc4703	12.821936	-9.108417
ngc4704	12.812897	41.92125
ngc4705	12.823603	-5.195861
ngc4706	12.831708	-41.279556
ngc4707	12.806353	51.164694
ngc4708	12.828189	-11.093028
ngc4709	12.834411	-41.381972
ngc4710	12.827453	15.165444
ngc4712	12.826172	25.469944
ngc4713	12.832742	5.311417
ngc4714	12.838681	-13.324333
ngc4715	12.832744	27.822417
ngc4716	12.842531	-9.451111
ngc4717	12.842886	-9.463028
ngc4718	12.8424	-5.281917
ngc4719	12.835756	33.159139
ngc4720	12.845217	-4.155833
ngc4721	12.838867	27.324
ngc4723	12.850808	-13.236611
ngc4724	12.848289	-14.331861
ngc4725	12.840717	25.500806
ngc4726	12.846128	-14.268556
ngc4727,ngc4740	12.849233	-14.332944
ngc4728	12.841133	27.434917
ngc4729	12.862856	-41.132278
ngc4730	12.866797	-41.147306
ngc4731	12.850303	-6.393056
ngc4732	12.835306	52.850111
ngc4733	12.851883	10.912083
ngc4734	12.853581	4.859056
ngc4735	12.850481	28.927972
m94,ngc4736	12.848072	41.120444
ngc4737	12.848039	34.156861
ngc4738	12.852472	28.788056
ngc4739	12.8603	-8.410222
ngc4741	12.849867	47.671556
ngc4742	12.863344	-10.454722
ngc4743	12.871106	-41.390667
ngc4744	12.872111	-41.060028
ngc4745	12.857267	27.421278
ngc4746	12.865378	12.082972
ngc4747	12.862764	25.777083
ngc4748	12.870128	-13.414722
ngc4749	12.853325	71.636722
ngc4750	12.835353	72.874639
ngc4751	12.880775	-42.659917
ngc4752	12.858075	13.781806
ngc4753	12.872808	-1.199694
ngc4754	12.871528	11.313889
herschelsjewelbox,kappacruciscluster,ngc4755	12.893633	-60.356306
ngc4756	12.881286	-15.413278
ngc4757	12.880581	-10.310222
ngc4758	12.878903	15.848528
ngc4759	12.884778	-9.202222
ngc4760	12.885342	-10.494194
ngc4761	12.886058	-9.197806
ngc4762	12.882236	11.230806
ngc4763	12.890894	-17.005528
ngc4764	12.885175	-9.257639
ngc4765	12.887336	4.463111
ngc4766	12.885603	-10.378194
ngc4767	12.898042	-39.714306
ngc4767a	12.883744	-39.83525
ngc4767b	12.912508	-39.852278
ngc4768	12.888125	-9.531444
ngc4769	12.888356	-9.536
ngc4770	12.892264	-9.5415
ngc4771	12.889228	1.269083
ngc4772	12.891433	2.168389
ngc4773	12.893336	-8.63875
ngc4774	12.885056	36.822778
ngc4775	12.896028	-6.622167
ngc4776	12.884572	-9.199917
ngc4777	12.899594	-8.775722
ngc4778	12.884947	-9.203833
ngc4779	12.897456	9.710056
ngc4780	12.901453	-8.621111
ngc4780a	12.900844	-8.653806
ngc4781	12.906597	-10.537194
ngc4782	12.909922	-12.568639
ngc4783	12.910164	-12.557833
ngc4784	12.910283	-10.613056
ngc4785	12.890925	-48.749194
ngc4786	12.909006	-6.859417
ngc4787	12.901533	27.068639
ngc4788	12.904453	27.303694
ngc4789	12.905283	27.068028
ngc4789a	12.901458	27.149639
ngc4790	12.914428	-10.247833
ngc4791	12.912208	8.053111
ngc4792	12.917689	-12.497167
ngc4793	12.911283	28.938667
ngc4794	12.919583	-12.608472
ngc4795	12.917461	8.0655
ngc4796	12.917969	8.066222
ngc4797,ngc4798	12.915325	27.412694
ngc4799	12.920981	2.896639
ngc4800	12.9105	46.531167
ngc4801	12.910492	53.09
ngc4802,ngc4804	12.930456	-12.055306
ngc4803	12.926022	8.240417
ngc4805	12.923397	27.981306
ngc4806	12.936778	-29.502944
ngc4807	12.92475	27.521417
ngc4808	12.930264	4.304111
ngc4809	12.914183	2.654083
ngc4810	12.914222	2.640278
ngc4811	12.947878	-41.797194
ngc4812	12.947972	-41.813333
ngc4813	12.943367	-6.817833
ngc4814	12.922761	58.344111
ngc4815	12.966214	-64.96175
ngc4816	12.936708	27.745472
ngc4817	12.941617	27.94
ngc4818	12.946917	-8.525306
ngc4819	12.941072	26.987333
ngc4820	12.950156	-13.719333
ngc4821	12.941425	26.957
ngc4822	12.951039	-10.761833
ngc4823	12.957122	-13.698694
ngc4824	12.943436	27.432639
ngc4825	12.9534	-13.664833
blackeyegalaxy,evileyegalaxy,m64,ngc4826	12.945456	21.682972
ngc4827	12.945425	27.178639
ngc4828	12.945239	28.020444
ngc4829	12.9568	-13.7375
ngc4830	12.957753	-19.691278
ngc4831	12.960192	-27.292139
ngc4832	12.963203	-39.761694
ngc4833	12.993039	-70.874583
ngc4834	12.940356	52.295861
ngc4835	12.968844	-46.264222
ngc4835a	12.953647	-46.374694
ngc4836	12.959525	-12.744111
ngc4837	12.946972	48.298611
ngc4838	12.9656	-13.060083
ngc4839	12.956767	27.497806
ngc4840	12.959122	27.610333
ngc4841	12.959139	28.479444
ngc4841a	12.958875	28.476944
ngc4841b	12.959414	28.48225
ngc4842	12.959972	27.489167
ngc4842a	12.959956	27.49325
ngc4842b	12.960039	27.484806
ngc4843	12.966894	-3.621139
ngc4844	12.968961	-13.079917
ngc4845,ngc4910	12.966997	1.575833
ngc4846	12.963247	36.370722
ngc4847	12.974708	-13.140917
ngc4848	12.968233	28.24275
ngc4850	12.972733	27.967722
ngc4851	12.972697	28.14875
ngc4852	13.001219	-59.609444
ngc4853	12.976442	27.596333
ngc4854	12.979833	27.67475
ngc4855	12.988458	-13.231028
ngc4856	12.989242	-15.042167
ngc4857	12.955094	70.203444
ngc4858	12.9839	28.11575
ngc4859	12.983842	26.815667
ngc4860	12.984417	28.123694
ngc4863	12.995128	-14.029639
ngc4864	12.986975	27.977
ngc4865	12.988853	28.084306
ngc4866	12.990872	14.171056
ngc4867	12.987569	27.970722
ngc4868	12.985806	37.310333
ngc4869	12.989822	27.911583
ngc4870	12.988269	37.048361
ngc4871	12.991656	27.956444
ngc4872	12.992789	27.946944
ngc4873	12.992442	27.983611
ngc4874	12.993253	27.959278
ngc4875	12.993864	27.907333
ngc4876	12.995669	27.912472
ngc4877	13.007317	-15.283444
ngc4878	13.005603	-6.103833
ngc4879	13.007114	-6.111222
ngc4880	13.002936	12.483306
ngc4881	12.999333	28.247389
ngc4882,ngc4886	13.001233	27.987583
ngc4883	12.998892	28.034722
ngc4884,ngc4889	13.002258	27.977
ngc4885	13.009408	-6.853083
ngc4887	13.010906	-14.66625
ngc4888	13.010072	-6.075194
ngc4890	13.010867	-4.604333
ngc4891	13.013053	-13.425944
ngc4892	13.000981	26.898111
ngc4894	13.004589	27.967528
ngc4895	13.004981	28.202306
ngc4895a	13.002533	28.170389
ngc4896	13.00855	28.346222
ngc4897	13.014708	-13.449806
ngc4898	13.005	27.957222
ngc4898a	13.004908	27.955389
ngc4898b	13.005025	27.956556
ngc4899	13.015731	-13.944222
ngc4900	13.010864	2.501444
ngc4901	12.999003	47.205556
ngc4902	13.016592	-14.513639
ngc4903	13.022992	-30.934972
ngc4904	13.016294	-0.027611
ngc4905	13.025189	-30.868278
ngc4906	13.011047	27.923889
ngc4907	13.013556	28.158333
ngc4908	13.015128	28.007639
ngc4909	13.033847	-42.771417
ngc4911	13.015578	27.790833
ngc4912	13.026	29.130611
ngc4914	13.011931	37.315278
ngc4915	13.024506	-4.546528
ngc4916	13.0345	29.253444
ngc4917	13.015436	47.222111
ngc4918	13.030728	-4.500556
ngc4919	13.021553	27.809083
ngc4921	13.023931	27.885944
ngc4922	13.023583	29.311111
ngc4923	13.0255	27.847528
ngc4924	13.036903	-14.969833
ngc4925	13.035386	-7.710778
ngc4926	13.031592	27.624444
ngc4926a	13.035522	27.648306
ngc4927	13.032667	28.005889
ngc4928	13.050158	-8.084972
ngc4929	13.045667	28.045361
ngc4930	13.068131	-41.411583
ngc4931	13.050244	28.032472
ngc4932	13.043808	50.438417
ngc4933	13.066083	-11.497778
ngc4933c	13.066969	-11.490556
ngc4934	13.054511	28.030417
ngc4935	13.055897	14.3775
ngc4936	13.071358	-30.52625
ngc4937	13.080992	-47.219361
ngc4938	13.049331	51.318528
ngc4939	13.070664	-10.339611
ngc4940	13.083403	-47.236917
ngc4941	13.070317	-5.551611
ngc4943	13.062483	28.084222
ngc4944	13.063875	28.185722
ngc4945	13.090967	-49.468222
ngc4945a	13.109369	-49.690639
ngc4946	13.091494	-43.591139
ngc4947a	13.072453	-35.227778
ngc4948a	13.084942	-8.161333
ngc4949	13.071644	29.029528
ngc4950	13.093481	-43.500528
ngc4951	13.085472	-6.493833
ngc4952,ngc4962	13.082883	29.12225
ngc4953	13.102908	-37.58575
ngc4954,ngc4972	13.038853	75.404167
ngc4955	13.101339	-29.754278
ngc4956	13.083594	35.178028
ngc4957	13.086775	27.56975
ngc4958	13.096911	-8.020278
ngc4959	13.094731	33.178917
ngc4960,ngc4961	13.096547	27.734139
ngc4963	13.097764	41.721917
ngc4964	13.090239	56.322778
ngc4965	13.119272	-28.228194
ngc4966	13.104808	29.062861
ngc4967	13.093453	53.564278
ngc4968	13.118328	-23.677028
ngc4969	13.1175	13.636944
ngc4971	13.115267	28.548028
ngc4974	13.098858	53.659278
ngc4975	13.130611	-5.017472
ngc4976	13.143758	-49.506417
ngc4977	13.101231	55.656083
ngc4978	13.130703	18.4155
ngc4980	13.1528	-28.641778
ngc4981	13.146872	-6.777528
ngc4982	13.14615	-10.588667
ngc4983	13.140914	28.3205
ngc4984	13.149231	-15.516306
ngc4985	13.136694	41.676333
ngc4986	13.140128	35.206444
ngc4987	13.133072	51.929306
ngc4988	13.165106	-43.105722
ngc4989	13.154458	-5.396417
cocoongalaxy,ngc4990	13.154803	-5.272806
ngc4991	13.154197	2.347667
ngc4992	13.151556	11.634167
ngc4993,ngc4994	13.16325	-23.383889
ngc4995	13.161292	-7.833417
ngc4996	13.158858	0.857028
ngc4997	13.164361	-16.515472
ngc4998	13.136156	50.66375
ngc4999	13.159203	1.673056
ngc5000	13.163192	28.906944
ngc5001	13.159197	53.494278
ngc5002	13.177225	36.633917
ngc5003	13.143864	43.737528
ngc5004	13.183764	29.636694
ngc5004a	13.183806	29.578278
ngc5005	13.182286	37.059194
ngc5006	13.196047	-19.26175
ngc5007	13.153997	62.175028
ngc5009	13.179731	50.092861
ngc5010	13.207319	-15.797861
ngc5011	13.214406	-43.096222
ngc5011a	13.2027	-43.307861
ngc5012	13.193622	22.9155
ngc5013	13.202042	3.199056
ngc5014	13.192006	36.282139
ngc5015	13.206358	-4.336472
ngc5016	13.201856	24.095
ngc5017	13.215139	-16.765833
ngc5018	13.216953	-19.518194
ngc5019	13.211775	4.729667
ngc5020	13.211075	12.59975
ngc5021	13.201742	46.196139
ngc5022	13.225219	-19.546639
ngc5023	13.2035	44.041222
m53,ngc5024	13.215342	18.169111
ngc5025	13.212431	31.809389
ngc5026	13.237122	-42.961278
ngc5027	13.222497	6.061278
ngc5028	13.229406	-13.042472
ngc5029	13.210442	47.063278
ngc5030	13.231708	-16.490944
ngc5031	13.234228	-16.123111
ngc5032	13.224153	27.802389
ngc5033	13.224297	36.593944
ngc5034	13.205281	70.649361
ngc5035	13.247008	-16.492694
ngc5036	13.245233	-4.178583
ngc5037	13.249825	-16.590306
ngc5038	13.250592	-15.951806
ngc5039	13.247756	-4.158167
ngc5040	13.225733	51.258361
ngc5041	13.24235	30.705778
ngc5042	13.258617	-23.984056
ngc5043	13.270739	-60.0455
ngc5044	13.256658	-16.385528
ngc5045	13.279722	-63.416667
ngc5046	13.262533	-16.326833
ngc5047	13.263478	-16.518889
ngc5048	13.268994	-28.410528
ngc5049	13.266472	-16.397167
ngc5050	13.261592	2.878972
ngc5051	13.27225	-28.285694
ngc5052	13.259692	29.676083
ngc5053	13.274164	17.69775
ngc5054	13.282914	-16.634861
m63,ngc5055,sunflowergalaxy	13.263703	42.029278
ngc5056	13.270089	30.950333
ngc5057	13.274381	31.0315
ngc5058	13.281197	12.548222
ngc5059	13.282906	7.8445
ngc5060	13.287839	6.037444
ngc5061	13.301408	-26.837222
ngc5062	13.306561	-35.458667
ngc5063	13.307142	-35.352472
ngc5064	13.316647	-47.908667
ngc5065	13.291836	31.092694
ngc5066,ngc5069	13.307903	-10.233889
ngc5067	13.307711	-10.145278
ngc5068	13.315225	-21.039111
ngc5070,ngc5072	13.320156	-12.539889
ngc5071	13.310331	7.935528
ngc5073	13.322403	-14.844528
ngc5074	13.307158	31.469083
ngc5075	13.318403	7.831028
ngc5076	13.325111	-12.740861
ngc5077	13.325464	-12.656972
ngc5078	13.33055	-27.410389
ngc5079	13.327236	-12.699028
ngc5080	13.322006	8.429139
ngc5081	13.318956	28.506917
ngc5082	13.344453	-43.699944
ngc5083	13.317528	39.589333
ngc5084	13.338033	-21.827583
ngc5085	13.338264	-24.440139
ngc5086	13.349836	-43.733528
ngc5087	13.340267	-20.611
ngc5088	13.338958	-12.571778
ngc5089	13.3276	30.256556
ngc5090	13.353561	-43.704556
ngc5090a	13.322531	-43.649389
ngc5090b	13.3382	-43.864667
ngc5091	13.354922	-43.719667
ngc5092	13.330981	22.999889
ngc5093	13.327169	40.386111
ngc5094	13.346347	-14.080667
ngc5095	13.343575	-2.289333
ngc5096	13.33575	33.089444
ngc5097	13.349914	-12.47125
ngc5098	13.337833	33.144167
ngc5099	13.355436	-13.042361
ngc5100	13.349611	8.981944
ngc5101	13.362844	-27.430528
ngc5102	13.366003	-36.63025
ngc5103	13.341689	43.083972
ngc5104	13.356414	0.342389
ngc5105	13.363636	-13.206778
ngc5106	13.349886	8.978306
ngc5107	13.356856	38.537611
ngc5108	13.388567	-32.342111
ngc5109,ngc5113	13.347875	57.64475
ngc5110,ngc5111	13.382367	-12.964806
ngc5112	13.365667	38.734694
ngc5114	13.400481	-32.343944
ngc5115	13.383439	13.950667
ngc5116	13.382114	26.980722
ngc5117	13.382356	28.316444
ngc5119	13.400089	-12.276444
ngc5120	13.427614	-63.458333
ngc5121	13.412669	-37.682194
ngc5121a	13.425778	-37.378806
ngc5122	13.40415	-10.654278
ngc5123	13.386256	43.08625
ngc5125	13.400197	9.710194
ngc5126	13.414889	-30.333611
ngc5127	13.395839	31.56575
centaurusa,ngc5128	13.424339	-43.019111
ngc5129	13.402781	13.976528
ngc5130	13.407544	-10.210222
ngc5131	13.39915	30.988056
ngc5132	13.408028	14.092583
ngc5133	13.414697	-4.082
ngc5134	13.421819	-21.134167
ngc5135	13.428906	-29.833667
ngc5137	13.414583	14.077194
ngc5138	13.454225	-59.040944
ngc5139,omegacentauri	13.446081	-47.476861
ngc5140	13.439369	-33.868472
ngc5141	13.414289	36.378528
ngc5142	13.416975	36.3995
ngc5143	13.417022	36.437167
ngc5144	13.381583	70.512222
ngc5145	13.420533	43.267278
ngc5146	13.443747	-12.323972
ngc5147	13.438814	2.100861
ngc5148	13.444106	2.313722
ngc5149	13.435875	35.934417
ngc5150	13.46015	-29.56225
ngc5151	13.444678	16.873806
ngc5152	13.4642	-29.618611
ngc5153	13.465092	-29.618028
ngc5154	13.441261	36.010278
ngc5155	13.476414	-63.508694
ngc5156	13.478914	-48.916806
ngc5157	13.454681	32.030722
ngc5158	13.463047	17.778833
ngc5159	13.471158	2.982667
ngc5160	13.472667	5.995889
ngc5161	13.487197	-33.173833
ngc5162,ngc5174	13.490536	11.007889
ngc5163	13.448406	52.753528
ngc5164	13.453306	55.487167
ngc5165	13.47755	11.387056
ngc5166	13.470844	32.032389
ngc5167	13.477842	12.711194
ngc5168	13.518125	-60.939222
ngc5169	13.469458	46.672139
ngc5170	13.496886	-17.966417
ngc5171	13.489322	11.735111
ngc5172	13.488697	17.051917
ngc5173	13.473686	46.591639
ngc5175	13.490631	10.995139
ngc5176	13.490267	11.781472
ngc5177	13.490072	11.797028
ngc5178	13.491475	11.624778
ngc5179	13.491911	11.745833
ngc5180	13.490822	16.825833
ngc5181	13.495	13.304111
ngc5182	13.511419	-28.150306
ngc5183	13.501708	-1.720583
ngc5184	13.503192	-1.663139
ngc5185	13.500625	13.416056
ngc5186	13.501083	12.175194
ngc5187	13.496719	31.130139
ngc5188	13.524522	-34.794417
ngc5190	13.510708	18.134611
ngc5191	13.513156	11.20075
ngc5192	13.514356	-1.778694
ngc5193	13.531536	-33.234222
ngc5193a	13.5303	-33.239472
m51,ngc5194,whirlpoolgalaxy	13.497975	47.195167
ngc5195	13.499886	47.266139
ngc5196	13.522128	-1.615056
ngc5197	13.523647	-1.693056
ngc5198	13.503167	46.670778
ngc5199	13.511878	34.830667
ngc5200	13.528461	-0.030167
ngc5201	13.487836	53.081972
ngc5202	13.533475	-1.698778
ngc5203	13.537056	-8.786222
ngc5204	13.493475	58.418722
ngc5205	13.500994	62.511583
ngc5206	13.562217	-48.151167
ngc5207	13.537219	13.892389
ngc5208	13.541092	7.316444
ngc5209	13.54515	7.32725
ngc5210	13.547014	7.170083
ngc5211	13.551483	-1.035806
ngc5212	13.548903	7.28775
ngc5213	13.577611	4.133333
ngc5214	13.546861	41.871833
ngc5215	13.585611	-33.483889
ngc5215a	13.585183	-33.481
ngc5215b	13.586072	-33.482972
ngc5216	13.535247	62.700694
ngc5217	13.568314	17.856861
ngc5218	13.536217	62.76775
ngc5219,ngc5244	13.644917	-45.855972
ngc5220	13.599075	-33.453806
ngc5221	13.582194	13.8325
ngc5222	13.582417	13.743333
ngc5223	13.573672	34.690444
ngc5224	13.585794	6.481111
ngc5225	13.5556	51.490333
ngc5226	13.584339	13.922167
ngc5227	13.590156	1.410583
ngc5228	13.576406	34.777806
ngc5229	13.567453	47.915444
ngc5230	13.592189	13.676167
ngc5231	13.596736	2.998917
ngc5232	13.602294	-8.497722
ngc5233	13.587039	34.677444
ngc5234	13.624983	-49.836917
ngc5235	13.600392	6.585361
m83,ngc5236,southernpinwheelgalaxy	13.616931	-29.865417
ngc5237	13.627514	-42.846972
ngc5238	13.578475	51.613667
ngc5239	13.607278	7.369583
ngc5240	13.598667	35.58825
ngc5241	13.611075	-8.401889
ngc5242	13.618719	2.770583
ngc5243	13.604153	38.343917
ngc5245	13.623119	3.897417
ngc5246	13.624825	4.104444
ngc5247	13.634178	-17.884028
ngc5248	13.625561	8.885167
ngc5249	13.627083	15.972222
ngc5250	13.602036	51.235806
ngc5251	13.623564	27.419222
ngc5252	13.637767	4.542583
ngc5253	13.665544	-31.640111
ngc5254	13.660531	-11.493861
ngc5255	13.6217	57.108944
ngc5256	13.638194	48.276944
ngc5257	13.664697	0.84
ngc5258	13.666025	0.830944
ngc5259	13.656639	30.991389
ngc5260	13.672194	-23.858083
ngc5261	13.671136	5.076306
ngc5262	13.59405	75.039417
ngc5263	13.665456	28.400583
ngc5264	13.693522	-29.913083
ngc5265	13.669197	36.861083
ngc5266	13.717253	-48.169417
ngc5266a	13.676972	-48.341972
ngc5267	13.677767	38.794083
ngc5268	13.703497	-13.859556
ngc5269	13.745611	-62.9125
ngc5270	13.703022	4.262583
ngc5271	13.695114	30.125444
m3,ngc5272	13.703119	28.375444
ngc5274	13.706475	29.847833
ngc5275	13.706544	29.824889
ngc5276	13.706111	35.624139
ngc5277	13.710661	29.954417
ngc5278	13.694339	55.670639
ngc5279	13.695486	55.673806
ngc5280	13.715428	29.868611
ngc5281	13.776431	-62.916528
ngc5282	13.723578	30.069528
ngc5283	13.684933	67.672306
ngc5284	13.789806	-59.149389
ngc5285	13.740497	2.109917
ngc5286	13.77405	-51.373472
ngc5287	13.747928	29.770917
ngc5288	13.812483	-64.685389
ngc5289	13.752419	41.503389
ngc5290	13.755328	41.712583
ngc5291	13.790133	-30.407
ngc5292	13.794464	-30.939528
ngc5293	13.7813	16.272861
ngc5294	13.755036	55.290833
ngc5295	13.644275	79.458889
ngc5296	13.77185	43.851361
ngc5297	13.773242	43.872333
ngc5298	13.810136	-30.428528
ngc5299	13.840628	-59.947722
ngc5300	13.804456	3.950861
ngc5301	13.773519	46.107056
ngc5302	13.8138	-30.511111
ngc5303	13.795831	38.304639
ngc5304	13.833744	-30.578472
ngc5305	13.798817	37.826333
ngc5306	13.819833	-7.224389
ngc5307	13.850917	-51.205778
ngc5308	13.783453	60.973167
ngc5309	13.836322	-15.618417
ngc5310	13.829928	0.069194
ngc5311	13.815578	39.985111
ngc5312	13.830714	33.62175
ngc5313	13.828983	39.984778
ngc5314	13.769833	70.339556
ngc5315	13.899136	-66.514167
ngc5316	13.899228	-61.869111
ngc5317,ngc5364	13.936667	5.014472
ngc5318	13.843336	33.704889
ngc5319	13.844628	33.761556
ngc5320	13.838994	41.366222
ngc5321	13.845469	33.632611
ngc5322	13.820908	60.190528
ngc5323	13.760144	76.828333
ngc5324	13.868303	-6.058306
ngc5325	13.848392	38.274778
ngc5326	13.847417	39.574861
ngc5327	13.867825	-2.206611
ngc5328	13.881475	-28.489389
ngc5329	13.869469	2.325111
ngc5330	13.883108	-28.470667
ngc5331	13.871194	2.103028
ngc5332	13.868867	16.96975
ngc5333	13.906728	-48.512528
ngc5335	13.882378	2.814278
ngc5336	13.869389	43.242917
ngc5337	13.873064	39.68725
ngc5338	13.890708	5.207778
ngc5339	13.900075	-7.930667
ngc5340	13.816642	72.653833
ngc5341	13.875544	37.817417
ngc5342	13.857181	59.863944
ngc5343	13.903253	-7.588139
ngc5344	13.832786	73.952889
ngc5345	13.903958	-1.436472
ngc5346	13.883858	39.580778
ngc5347	13.888286	33.490833
ngc5348	13.903131	5.227444
ngc5349	13.886981	37.883139
ngc5350	13.889342	40.363944
ngc5351	13.891031	37.914972
ngc5352	13.894008	36.134056
ngc5353	13.890747	40.283028
ngc5354	13.89075	40.30275
ngc5355	13.895989	40.338667
ngc5356	13.916239	5.333722
ngc5357	13.933208	-30.341444
ngc5358	13.900114	40.277306
ngc5359	14.002658	-70.392306
ngc5361	13.909786	38.449417
ngc5362	13.914806	41.313528
ngc5363	13.935336	5.254778
ngc5365	13.964067	-43.931306
ngc5365a	13.944314	-44.00925
ngc5365b	13.977658	-43.963722
ngc5366	13.940239	-0.247556
ngc5368	13.9081	54.330667
ngc5369	13.943783	-5.469889
ngc5370	13.902603	60.678056
ngc5371,ngc5390	13.927761	40.46175
ngc5372	13.912775	58.666861
ngc5373	13.952072	5.251889
ngc5374	13.958231	6.097
ngc5375,ngc5396	13.948889	29.164361
ngc5376	13.921131	59.506611
ngc5377	13.937964	47.235694
ngc5378	13.947506	37.79725
ngc5379	13.9262	59.742806
ngc5380	13.949081	37.610389
ngc5381	14.011656	-59.586806
ngc5382	13.970803	6.258694
ngc5383	13.951381	41.84625
ngc5384	13.970239	6.518194
ngc5385	13.875533	76.162778
ngc5386	13.972872	6.339111
ngc5387	13.973553	6.071278
ngc5388	13.982769	-14.150889
ngc5389	13.935092	59.742056
ngc5391	13.961883	46.469583
ngc5392	13.990214	-3.209194
ngc5393	14.0089	-28.874583
ngc5394	13.976014	37.453472
ngc5395	13.977217	37.424472
ngc5397	14.019572	-33.945833
ngc5398	14.022656	-33.063778
ngc5399	13.992061	34.773583
ngc5400	14.010333	-2.857806
ngc5401	13.995397	36.238111
ngc5402	13.971264	59.814556
ngc5403	13.997478	38.182528
ngc5404	14.018744	0.085889
ngc5405	14.019297	7.702278
ngc5406	14.005589	38.915417
ngc5407	14.013917	39.156222
ngc5408	14.055808	-41.377694
ngc5409	14.029467	9.490278
ngc5410	14.015169	40.988611
ngc5411	14.033128	8.937694
ngc5412	13.953758	73.616722
ngc5413	13.964869	64.910972
ngc5414	14.034311	9.929306
ngc5415	13.949144	70.754389
ngc5416	14.036478	9.440111
ngc5417	14.036956	8.037111
ngc5418	14.038219	7.684167
ngc5419	14.060758	-33.97825
ngc5420	14.066639	-14.616861
ngc5421	14.0283	33.823778
ngc5422	14.011678	55.164472
ngc5423	14.046839	9.341389
ngc5424	14.048806	9.420667
ngc5425	14.013242	48.443861
ngc5426	14.056903	-6.069111
ngc5427	14.057236	-6.030806
ngc5428	14.057786	-5.984472
ngc5429	14.059267	-6.038278
ngc5430	14.012706	59.328278
ngc5431	14.051986	9.363056
ngc5432	14.061292	-5.975444
ngc5433	14.043356	32.510444
ngc5434	14.056428	9.448083
ngc5435	14.066681	-5.931667
ngc5436	14.061417	9.5735
ngc5438,ngc5446	14.063333	9.610583
ngc5439	14.032686	46.311917
ngc5440	14.050289	34.757861
ngc5441	14.053333	34.684611
ngc5442	14.078672	-9.713667
ngc5443	14.036611	55.814028
ngc5444	14.056703	35.132111
ngc5445	14.05875	35.025306
ngc5447	14.041222	54.276917
ngc5448	14.047231	49.172694
ngc5449	14.040908	54.330222
ngc5450	14.041608	54.271028
ngc5451	14.043625	54.362528
ngc5452	13.906917	78.220556
ngc5453	14.048997	54.307972
ngc5454	14.079364	14.382056
ngc5455	14.050325	54.241472
ngc5456	14.083025	11.871639
m101,m102,ngc5457	14.053483	54.348944
ngc5458	14.053464	54.298333
ngc5459	14.083386	13.131889
ngc5460	14.124392	-48.342528
ngc5461	14.061503	54.318028
ngc5462	14.064722	54.365583
ngc5463	14.102928	9.353444
ngc5464	14.117889	-30.017111
ngc5465	14.107578	-5.506278
ngc5466	14.090933	28.5345
ngc5468	14.109692	-5.453111
ngc5469	14.208306	8.647944
ngc5470	14.108864	6.029694
ngc5471	14.074728	54.396917
ngc5472	14.115283	-5.460472
ngc5473	14.078675	54.892639
ngc5474	14.083781	53.662222
ngc5475	14.086781	55.741861
ngc5476	14.135692	-6.092056
ngc5477	14.092583	54.461139
ngc5478	14.135697	-1.702306
ngc5479	14.099269	65.69075
ngc5480	14.105994	50.725111
ngc5481	14.111464	50.723333
ngc5482	14.141861	8.931917
ngc5483	14.173619	-43.324611
ngc5484	14.113394	55.029917
ngc5485	14.119819	55.001694
ngc5486	14.1236	55.103083
ngc5487	14.162194	8.069139
ngc5489	14.2002	-46.088722
ngc5490	14.165914	17.545556
ngc5490c	14.168586	17.61575
ngc5491	14.182597	6.364861
ngc5492	14.176444	19.612333
ngc5493	14.191494	-5.043611
ngc5494	14.206717	-30.644083
ngc5495	14.206486	-27.108028
ngc5496	14.19385	-1.159111
ngc5497	14.175456	38.893556
ngc5498	14.184592	25.697972
ngc5499	14.179903	35.9135
ngc5500	14.170897	48.546111
ngc5501	14.205606	1.272528
ngc5502,ngc5503	14.159431	60.409583
ngc5504	14.204392	15.841917
ngc5504c	14.204386	15.879333
ngc5505	14.208808	13.304722
ngc5506	14.220803	-3.207583
ngc5507	14.222186	-3.148889
ngc5508	14.208067	24.6355
ngc5509	14.210994	20.387
ngc5510	14.227006	-17.983806
ngc5511	14.218172	8.631889
ngc5512	14.211425	30.855056
ngc5513	14.219064	20.416278
ngc5514	14.227439	7.659528
ngc5515	14.210603	39.310278
ngc5516	14.265192	-48.114861
ngc5517	14.214233	35.710889
ngc5518	14.229911	20.848306
ngc5519,ngc5570	14.239131	7.515917
ngc5520	14.206331	50.348417
ngc5521	14.256589	4.408528
ngc5522	14.247325	15.146889
ngc5523	14.247867	25.317611
ngc5524	14.233511	36.417361
ngc5525	14.260897	14.282611
ngc5526	14.2316	57.771333
ngc5527	14.240897	36.4045
ngc5528	14.2722	8.293472
ngc5529	14.259464	36.226583
ngc5530	14.307542	-43.388583
ngc5531	14.278694	10.884778
ngc5532	14.281375	10.807389
ngc5533	14.268817	35.343833
ngc5534	14.294517	-7.417417
ngc5535	14.292019	8.208389
ngc5536	14.273294	39.502194
ngc5537	14.293636	7.055
ngc5538	14.295136	7.476667
ngc5539	14.293825	8.179611
ngc5540	14.248453	60.011111
ngc5541	14.2755	39.589056
ngc5542	14.298111	7.558778
ngc5543	14.301131	7.654861
ngc5544	14.284033	36.571583
ngc5545	14.284767	36.575111
ngc5546	14.302564	7.564556
ngc5547	14.162556	78.601056
ngc5548	14.299869	25.136778
ngc5549	14.310781	7.377333
ngc5550	14.307769	12.883083
ngc5551	14.315233	5.451472
ngc5552,ngc5558	14.317736	7.031694
ngc5553	14.308258	26.287833
ngc5554,ngc5564	14.320833	7.021139
ngc5555	14.313356	-19.138917
ngc5556	14.342803	-29.241778
ngc5557	14.307144	36.493556
ngc5559	14.320217	24.798722
ngc5560	14.334581	3.992472
ngc5561	14.289675	58.7505
ngc5562	14.336403	10.262833
ngc5563	14.336969	7.055417
ngc5565	14.321806	6.994944
ngc5566	14.338858	3.93375
ngc5567	14.321567	35.137944
ngc5568	14.322589	35.092167
ngc5569	14.342247	3.983222
ngc5571	14.325564	35.150944
ngc5572	14.326472	36.140667
ngc5573	14.344864	6.907306
ngc5574	14.348881	3.238
ngc5575,ngc5578	14.349836	6.202667
ngc5576	14.351022	3.271
ngc5577	14.353642	3.435778
ngc5579	14.340689	35.188806
ngc5580,ngc5590	14.360669	35.204861
ngc5581	14.354531	23.480028
ngc5582	14.345311	39.693583
ngc5583	14.36125	13.232389
ngc5584	14.373269	-0.387667
ngc5585	14.330056	56.729056
ngc5586	14.368794	13.184278
ngc5587	14.369642	13.918056
ngc5588,ngc5589	14.356975	35.270639
ngc5591	14.376111	13.716667
ngc5592	14.398625	-28.688056
ngc5593	14.42755	-54.798694
ngc5595	14.403678	-16.723
ngc5596	14.37465	37.122194
ngc5597	14.407622	-16.76275
ngc5598	14.374522	40.319806
ngc5599	14.397392	6.576111
ngc5600	14.397089	14.638778
ngc5601	14.381467	40.309583
ngc5602	14.371897	50.501389
ngc5603	14.383758	40.377417
ngc5604	14.411889	-3.212167
ngc5605	14.418769	-13.163
ngc5606	14.463133	-59.63225
ngc5608	14.388303	41.775889
ngc5609	14.39675	34.842778
ngc5610	14.406372	24.614139
ngc5611	14.401328	33.047389
ngc5612	14.567014	-78.3875
ngc5613	14.401656	34.892111
ngc5614	14.402108	34.858861
ngc5615	14.401806	34.865
ngc5616	14.40575	36.461417
ngc5617	14.495575	-60.710833
ngc5618	14.453281	-2.262417
ngc5619	14.455064	4.802833
ngc5621	14.463836	8.24025
ngc5622	14.436719	48.564
ngc5623	14.452411	33.252556
ngc5624	14.443114	51.585361
ngc5625	14.450417	39.956944
ngc5626	14.496969	-29.748472
ngc5627	14.476189	11.37825
ngc5628	14.473831	17.924361
ngc5629	14.471214	25.848778
ngc5630	14.460169	41.25775
ngc5631	14.442583	56.582639
ngc5632,ngc5691	14.631483	-0.398889
ngc5633	14.457883	46.146528
ngc5634	14.493689	-5.976417
ngc5635	14.475489	27.408944
ngc5636	14.494172	3.266306
ngc5637	14.483222	23.1915
ngc5638	14.49455	3.233306
ngc5639	14.479597	30.412944
ngc5640	14.344669	80.123111
ngc5641	14.48795	28.821889
ngc5642	14.487081	30.026444
ngc5643	14.54465	-44.174417
ngc5644	14.507106	11.928
ngc5645	14.510931	7.275083
ngc5646	14.492781	35.461944
ngc5647	14.510028	11.876694
ngc5648,ngc5649	14.509056	14.023056
ngc5650,ngc5652	14.516967	5.978417
ngc5651,ngc5713	14.669864	-0.288972
ngc5654	14.500369	36.360917
ngc5655	14.514147	13.96875
ngc5656	14.507086	35.321028
ngc5657	14.512111	29.180833
ngc5658,ngc5719	14.682322	-0.318222
ngc5659	14.518372	25.355111
ngc5660	14.497169	49.622667
ngc5661	14.532608	6.250417
ngc5662	14.593772	-56.618083
ngc5663	14.565639	-16.581056
ngc5665	14.540483	8.078639
ngc5665a	14.540928	8.078722
ngc5666	14.552558	10.510806
ngc5667	14.506364	59.469778
ngc5668	14.556761	4.450444
ngc5669	14.545414	9.890444
ngc5670	14.593342	-45.966972
ngc5671	14.461667	69.694167
ngc5673	14.525253	49.958722
ngc5674	14.564511	5.458222
ngc5675	14.544397	36.302194
ngc5676	14.546347	49.457889
ngc5677	14.570206	25.468028
ngc5678	14.534892	57.921444
ngc5679	14.58575	5.356389
ngc5679a	14.585108	5.356833
ngc5679b	14.585767	5.358944
ngc5679c	14.586386	5.354278
ngc5680	14.595703	-0.013361
ngc5681	14.595242	8.300611
ngc5682	14.579161	48.67025
ngc5683	14.581236	48.661917
ngc5684	14.597267	36.543222
ngc5685	14.604269	29.908389
ngc5686	14.600719	36.503194
ngc5687	14.581222	54.475861
ngc5688	14.659764	-45.019
ngc5689	14.591581	48.741639
ngc5690	14.628075	2.290833
ngc5692	14.638364	3.410333
ngc5693	14.603108	48.585028
ngc5694	14.660142	-26.538333
ngc5695	14.622811	36.567806
ngc5696	14.615856	41.828111
ngc5698	14.62075	38.454278
ngc5699,ngc5706	14.6451	30.465917
ngc5700	14.6171	48.544833
ngc5701	14.653078	5.363472
ngc5702	14.648633	20.506722
ngc5703,ngc5709	14.647228	30.442528
ngc5704,ngc5708	14.637856	40.45675
ngc5705	14.663803	-0.718472
ngc5707	14.625214	51.561861
ngc5710	14.654497	20.043694
ngc5711	14.656267	19.990889
ngc5712	14.494922	78.86425
ngc5714	14.636533	46.63825
ngc5715	14.724914	-57.577028
ngc5716	14.684867	-17.476972
ngc5717	14.643803	46.663139
ngc5718	14.678567	3.465417
ngc5720	14.642581	50.815222
ngc5721	14.648044	46.674444
ngc5722	14.648447	46.665611
ngc5723	14.649422	46.689611
ngc5724	14.650592	46.692028
ngc5725	14.682867	2.186556
ngc5726	14.715569	-18.444889
ngc5727	14.673922	33.989111
ngc5728	14.706639	-17.253083
ngc5729	14.701911	-9.009444
ngc5730	14.664489	42.742361
ngc5732	14.677486	38.637806
ngc5733	14.712758	-0.351083
ngc5734	14.752514	-20.870472
ngc5735	14.709233	28.726444
ngc5736	14.725225	11.202694
ngc5737	14.71995	18.879944
ngc5738	14.732325	1.604167
ngc5739	14.708031	41.842333
ngc5740	14.740125	1.679778
ngc5741	14.764367	-11.914278
ngc5742	14.760244	-11.809639
ngc5743	14.753053	-20.9135
ngc5744	14.777403	-18.513278
ngc5745	14.7506	-13.946222
ngc5746	14.748867	1.955
ngc5748	14.751419	21.916222
ngc5749	14.814983	-54.497694
ngc5750	14.769756	-0.222944
ngc5751	14.730328	53.400667
ngc5752	14.753933	38.728861
ngc5753	14.755244	38.805889
ngc5754	14.755458	38.731222
ngc5755	14.756811	38.779889
ngc5756	14.792703	-14.853583
ngc5757	14.796217	-19.078556
ngc5758	14.783911	13.668389
ngc5759	14.787392	13.457944
ngc5760	14.795072	18.502028
ngc5761	14.819022	-20.376028
ngc5762	14.811825	12.457222
ngc5763	14.816311	12.490139
ngc5764	14.892289	-52.670528
ngc5765	14.8475	5.116944
ngc5765a	14.847417	5.119444
ngc5765b	14.847642	5.114472
ngc5766	14.885989	-21.394111
ngc5767	14.826231	47.376167
ngc5768	14.868875	-2.52975
ngc5769	14.878203	7.931806
ngc5770	14.887506	3.959722
ngc5771	14.870647	29.845417
ngc5772	14.8608	40.599167
ngc5773	14.875117	29.807389
ngc5774	14.895128	3.5825
ngc5775	14.899333	3.544444
ngc5776	14.909097	2.966444
ngc5777	14.854958	58.977944
ngc5778,ngc5825	14.908747	18.642306
ngc5779	14.869322	55.899444
ngc5780	14.906297	28.939667
ngc5781	14.944783	-17.243944
ngc5782	14.932019	11.861528
ngc5783,ngc5785	14.891197	52.076111
ngc5784	14.904569	42.557917
ngc5786	14.982294	-42.013361
ngc5787	14.920994	42.506861
ngc5788	14.888053	52.04425
ngc5789	14.9432	30.234028
ngc5790	14.959947	8.285278
ngc5791	14.979506	-19.266861
ngc5792	14.972975	-1.091083
ngc5793	14.990211	-16.693361
ngc5794	14.931564	49.726083
ngc5795	14.938856	49.400056
ngc5796	14.990031	-16.623861
ngc5797	14.940014	49.696167
ngc5798	14.960547	29.9685
ngc5799	15.093114	-72.432833
ngc5800	15.029964	-51.918583
ngc5801	15.007206	-13.904306
ngc5802	15.008333	-13.919028
ngc5803	15.009594	-13.894528
ngc5804	14.951889	49.669028
ngc5805	14.953306	49.627778
ngc5806	15.000111	1.891306
ngc5807	14.930186	63.903472
ngc5808,ngc5819	14.900781	73.131694
ngc5809	15.014536	-14.165194
ngc5810	15.045203	-17.868
ngc5811	15.007472	1.623889
ngc5812	15.015472	-7.457361
ngc5813	15.019786	1.701972
ngc5814	15.022542	1.637083
ngc5815	15.008136	-16.834306
ngc5816	15.00135	-16.093639
ngc5817	14.994681	-16.180361
ngc5818	14.982886	49.821417
ngc5820	14.977728	53.886083
ngc5821	14.983239	53.923278
ngc5822	15.072569	-54.396417
ngc5823	15.091842	-55.60375
ngc5824,ngc5834	15.066289	-33.068139
ngc5826,ngc5870	15.1094	55.479111
ngc5827	15.031592	25.964528
ngc5828	15.012808	49.993667
ngc5829	15.045003	23.333611
ngc5830	15.030808	47.875389
ngc5831	15.068611	1.219917
ngc5832	14.962697	71.682333
ngc5833	15.198236	-72.859417
ngc5835	15.040381	48.877694
ngc5836	14.991942	73.893222
ngc5837	15.077939	12.633444
ngc5838	15.090628	2.099333
ngc5839	15.090969	1.634806
ngc5840	15.072375	29.506028
ngc5841,ngc5848	15.109733	2.004806
ngc5842	15.081108	21.069444
ngc5843	15.124414	-36.327417
ngc5844	15.178042	-64.673667
ngc5845	15.100225	1.633806
ngc5846	15.108133	1.605611
ngc5846a	15.108111	1.594861
ngc5847	15.106186	6.379889
ngc5849	15.114081	-14.571833
ngc5850	15.118803	1.54425
ngc5851	15.114839	12.858861
ngc5852	15.115669	12.846833
ngc5853	15.098136	39.522194
ngc5854	15.129917	2.568639
ngc5855	15.130289	3.984167
ngc5856	15.122286	18.442444
ngc5857	15.124253	19.597639
ngc5858	15.146983	-11.207833
ngc5859	15.126317	19.582306
ngc5860	15.109389	42.641389
ngc5861	15.154469	-11.321667
ngc5862	15.100919	55.573861
ngc5863	15.1801	-18.431028
ngc5864	15.159322	3.05275
ngc5865,ngc5868	15.163661	0.529833
ngc5866	15.108194	55.763222
ngc5866b	15.202008	55.785083
ngc5867	15.106756	55.731583
ngc5869	15.163733	0.470028
ngc5871	15.167997	0.498
ngc5872	15.182128	-11.480139
ngc5873	15.214111	-38.125556
ngc5874	15.131064	54.752778
ngc5875	15.153656	52.528444
ngc5877	15.214742	-4.927222
ngc5878	15.229364	-14.269833
ngc5879	15.162981	57.000194
ngc5880	15.250317	-14.579028
ngc5883	15.252828	-14.617056
ngc5884	15.219203	31.861056
ngc5885	15.251156	-10.086
ngc5886	15.212622	41.233583
ngc5887	15.24555	1.15425
ngc5888	15.218714	41.264639
ngc5889	15.221042	41.327972
ngc5890	15.297547	-17.589194
ngc5891	15.270389	-11.49425
ngc5892	15.230058	-15.463889
ngc5893	15.226158	41.958806
ngc5894	15.194717	59.808944
ngc5895	15.230556	42.008083
ngc5896	15.230744	42.024278
ngc5897	15.290111	-21.010111
ngc5898	15.303767	-24.097944
ngc5899	15.250894	42.049833
ngc5900	15.251433	42.209417
ngc5901	15.250722	42.228056
ngc5902	15.239556	50.329667
ngc5903	15.310147	-24.068583
m5,ngc5904	15.309375	2.082694
ngc5905	15.256478	55.517361
ngc5906,ngc5907	15.264936	56.328778
ngc5908	15.278672	55.40925
ngc5909	15.191119	75.383806
ngc5910	15.323639	20.895
ngc5911	15.338394	3.518333
ngc5912	15.194694	75.384806
ngc5913	15.348733	-2.577944
ngc5914	15.312172	41.865472
ngc5914b	15.312586	41.890806
ngc5915	15.359189	-13.09175
ngc5916	15.360533	-13.169278
ngc5916a	15.353844	-13.100611
ngc5917	15.359047	-7.377167
ngc5918	15.323683	45.88025
ngc5919	15.360244	7.719306
ngc5920	15.364403	7.708806
ngc5921	15.365711	5.070528
ngc5922,ngc5923	15.353956	41.725944
ngc5924	15.367217	31.233083
ngc5925	15.45745	-54.528778
ngc5926	15.39025	12.715278
ngc5927	15.466786	-50.672778
ngc5928	15.434133	18.073639
ngc5929	15.435044	41.670667
ngc5930	15.435539	41.676056
ngc5931	15.491564	7.57325
ngc5932	15.446725	48.614972
ngc5933	15.450436	48.613306
ngc5934	15.470217	42.929917
ngc5935	15.471308	42.944111
ngc5936	15.500231	12.989333
ngc5937	15.512814	-2.8295
ngc5938	15.607297	-66.85975
ngc5939	15.412786	68.730639
ngc5940	15.521686	7.45775
ngc5941	15.527844	7.339
ngc5942	15.526894	7.312417
ngc5943	15.495589	42.777972
ngc5944	15.529889	7.308139
ngc5945	15.495839	42.918667
ngc5947	15.510167	42.717139
ngc5948	15.549622	3.982833
ngc5949	15.466853	64.763194
ngc5950	15.525219	40.430028
ngc5951	15.561961	15.007278
ngc5952	15.582344	4.958833
ngc5953	15.575661	15.193778
ngc5954	15.576394	15.200056
ngc5955	15.5868	5.063
ngc5956	15.582928	11.750278
ngc5957	15.589781	12.047611
ngc5958	15.580319	28.65525
ngc5959	15.622897	-16.595778
ngc5960	15.605119	5.665361
ngc5961	15.587867	30.864167
ngc5962	15.6088	16.607778
ngc5963	15.557739	56.559694
ngc5965	15.56735	56.685611
ngc5966	15.597817	39.768944
ngc5967	15.804425	-75.672944
ngc5967a	15.782978	-75.787444
ngc5968	15.665881	-30.552778
ngc5969	15.580839	56.451083
ngc5970	15.641658	12.186611
ngc5971	15.593581	56.461694
ngc5972	15.648381	17.026194
ngc5973	15.670964	-8.600944
ngc5974	15.650672	31.759917
ngc5975	15.666103	21.470806
ngc5976	15.613325	59.39775
ngc5977	15.675958	17.127972
ngc5978	15.707561	-13.234444
ngc5979	15.794739	-61.217861
ngc5980	15.691778	15.787667
ngc5981	15.631514	59.39175
ngc5982	15.644397	59.355833
ngc5983	15.712675	8.241111
ngc5984	15.714769	14.231472
ngc5985	15.660303	59.331944
ngc5986	15.767622	-37.786139
ngc5987	15.665936	58.079528
ngc5988	15.742739	10.293139
ngc5989	15.692444	59.755222
ngc5990	15.771211	2.415417
ngc5991	15.754661	24.630528
ngc5992	15.739308	41.086361
ngc5993	15.741006	41.120806
ngc5994	15.781461	17.872611
ngc5995	15.806931	-13.757778
ngc5996	15.783022	17.884194
ngc5997	15.791019	8.321194
ngc5998	15.827281	-28.578222
ngc5999	15.869064	-56.472806
ngc6000	15.830431	-29.386833
ngc6001	15.7961	28.641694
ngc6002	15.795664	28.609694
ngc6003	15.823789	19.032083
ngc6004	15.839644	18.939278
ngc6005	15.930194	-57.437389
ngc6006	15.884047	12.005361
ngc6007	15.889772	11.959194
ngc6008	15.882231	21.1005
ngc6009	15.890022	12.058667
ngc6010	15.905319	0.543056
ngc6011	15.775803	72.169222
ngc6012	15.903872	14.60125
ngc6013	15.881344	40.646722
ngc6015	15.857008	62.310028
ngc6016	15.931908	26.9665
ngc6017	15.954289	5.998389
ngc6018	15.958269	15.872611
ngc6019	15.869206	64.840667
ngc6021	15.958525	15.956056
ngc6022	15.963269	16.282306
ngc6023	15.963783	16.310194
ngc6024	15.885519	64.918056
ngc6025	16.054942	-60.431361
ngc6026	16.022475	-34.544222
ngc6027	15.986817	20.763361
ngc6027a	15.986428	20.754861
ngc6027b	15.986342	20.762194
ngc6027c	15.986631	20.747611
ngc6027d	15.986917	20.759917
ngc6027e	15.987356	20.765917
ngc6028,ngc6046	16.024711	19.359889
ngc6029	16.033019	12.574
ngc6030	16.03095	17.9575
ngc6031	16.126494	-54.014944
ngc6032	16.050311	20.955944
ngc6033	16.074439	-2.120972
ngc6034	16.058911	17.198694
ngc6035	16.056717	20.89125
ngc6036	16.075208	3.868472
ngc6037	16.074972	3.815139
ngc6038	16.044597	37.3595
ngc6039,ngc6042	16.077658	17.700861
ngc6040	16.074064	17.745139
ngc6041	16.076467	17.71925
ngc6043	16.083667	17.773889
ngc6045	16.085525	17.757667
ngc6047	16.085831	17.729889
ngc6048	15.958403	70.689111
ngc6049	16.093869	8.09625
ngc6050	16.089825	17.757167
ngc6051	16.082408	23.932694
ngc6052,ngc6064	16.086942	20.542361
ngc6053,ngc6057	16.092378	18.159583
ngc6055	16.094347	18.164361
ngc6058	16.074039	40.683056
ngc6059	16.113333	-6.393056
ngc6060	16.097772	21.484972
ngc6061	16.104453	18.249944
ngc6062	16.106339	19.777972
ngc6062b	16.105269	19.76325
ngc6063	16.120275	7.979
ngc6065	16.123044	13.887917
ngc6066	16.126486	13.943722
ngc6067	16.219736	-54.218944
ngc6068	15.923886	78.996778
ngc6068a	15.913197	78.985111
ngc6069	16.128233	38.93075
ngc6070	16.166303	0.709306
ngc6071	16.035286	70.417028
ngc6072	16.216167	-36.23
ngc6073	16.169681	16.699611
ngc6074	16.188056	14.256944
ngc6076	16.187056	26.8725
ngc6077	16.187256	26.923417
ngc6078	16.201514	14.208778
ngc6080	16.216389	2.179167
ngc6082	16.257656	-34.23275
ngc6083	16.220183	14.185417
ngc6084	16.237978	17.757444
ngc6085	16.209783	29.365083
ngc6086	16.209869	29.484778
ngc6087,snorcluster	16.31405	-57.934583
ngc6088	16.17875	57.464167
ngc6089	16.211306	33.036389
ngc6090	16.194639	52.456667
ngc6091	16.131386	69.904778
ngc6092	16.234611	28.125611
m80,ngc6093	16.284031	-22.975111
ngc6094	16.109417	72.494389
ngc6095	16.186381	61.267972
ngc6096	16.246306	26.558833
ngc6097	16.240603	35.109167
ngc6098	16.259494	19.461972
ngc6099	16.259878	19.453389
ngc6100	16.281214	0.841306
ngc6101	16.430158	-72.201556
ngc6102	16.260256	28.158583
ngc6103	16.262394	31.963944
ngc6104	16.275192	35.708056
ngc6105	16.285919	34.878889
ngc6106	16.313103	7.410889
ngc6107	16.288925	34.901944
ngc6108	16.290453	35.135722
ngc6109	16.294589	35.004278
ngc6110	16.295547	35.086972
ngc6111	16.239667	63.261111
ngc6112	16.300156	35.110278
ngc6113	16.319594	14.133639
ngc6114	16.306564	35.174306
ngc6115	16.407328	-51.94825
ngc6116	16.315167	35.153972
ngc6117	16.321711	37.095222
ngc6118	16.363506	-2.283444
ngc6119	16.328325	37.806306
ngc6120	16.330028	37.774472
m4,ngc6121	16.393167	-26.525528
ngc6122	16.335981	37.798222
ngc6123	16.288817	61.939111
ngc6124	16.422239	-40.653694
ngc6125,ngc6127,ngc6128	16.319875	57.984222
ngc6126	16.357758	36.376639
ngc6129	16.362019	37.996028
ngc6130	16.325956	57.614972
ngc6131	16.364514	38.932444
ngc6133	16.338114	56.652417
ngc6134	16.462917	-49.151167
ngc6135	16.240244	64.98275
ngc6136	16.349839	55.9705
ngc6137	16.384194	37.922361
ngc6138,ngc6363	17.377783	41.101694
ngc6139	16.461253	-38.84975
ngc6140	16.349489	65.390556
ngc6141	16.385114	40.858306
ngc6142	16.389186	37.258389
ngc6143	16.361747	55.086056
ngc6144	16.453928	-26.024722
ngc6145	16.417322	40.946639
ngc6146	16.419544	40.892861
ngc6147	16.418289	40.928778
ngc6148	16.451119	24.093278
ngc6149	16.456731	19.597194
ngc6150	16.430564	40.488556
ngc6151	16.640061	-73.252444
ngc6152	16.546006	-52.644
ngc6153	16.525178	-40.253444
ngc6154	16.425133	49.84025
ngc6155	16.43565	48.366806
ngc6156	16.581264	-60.618806
ngc6157	16.430108	55.360583
ngc6158	16.461358	39.383
ngc6159	16.457008	42.679722
ngc6160	16.461425	40.927
ngc6161	16.472397	32.810639
ngc6162	16.472881	32.849333
ngc6163	16.474419	32.846389
ngc6164	16.561622	-48.080056
ngc6165	16.567625	-48.1505
ngc6166	16.477356	39.551556
ngc6166b	16.481447	39.56
ngc6166c	16.473142	39.570306
ngc6167	16.576383	-49.771889
ngc6168	16.522583	20.184944
ngc6169	16.567953	-44.045639
ngc6170,ngc6176	16.460139	59.5625
m107,ngc6171	16.5422	-13.053639
ngc6173	16.495806	40.811611
ngc6174	16.496578	40.871972
ngc6175	16.499417	40.629167
ngc6177	16.5108	35.056444
ngc6178	16.596458	-45.64375
ngc6179	16.513069	35.10225
ngc6180	16.509422	40.539444
ngc6181	16.539156	19.826556
ngc6182	16.492778	55.517778
ngc6183	16.694972	-69.372167
ngc6184	16.526258	40.565611
ngc6185	16.554953	35.342333
ngc6186	16.573744	21.540889
ngc6187	16.526861	57.706667
ngc6188,rimnebula	16.668289	-48.662278
ngc6189	16.528028	59.626111
ngc6190	16.535194	58.438972
ngc6191	16.191803	58.785833
ngc6192	16.673297	-43.366806
ngc6193	16.688953	-48.762528
ngc6194	16.610319	36.200444
ngc6195	16.609047	39.027889
ngc6198	16.591847	57.486778
ngc6199	16.658047	36.058972
ngc6200	16.735375	-47.462667
ngc6201	16.670669	23.765333
ngc6202,ngc6226	16.723119	61.983944
ngc6203	16.674281	23.774833
ngc6204	16.769306	-47.016972
herculesglobularcluster,m13,ngc6205	16.694897	36.461306
ngc6207	16.717708	36.832417
ngc6208	16.824497	-53.728333
ngc6209	16.916017	-72.586639
ngc6210	16.741533	23.799833
ngc6211	16.691011	57.783639
ngc6212	16.723094	39.806444
ngc6213	16.693664	57.814861
ngc6214	16.658869	66.039528
ngc6215	16.851892	-58.993472
ngc6215a	16.883181	-58.948
ngc6216	16.823225	-44.731528
ngc6217	16.544222	78.198167
m12,ngc6218	16.787367	-1.947833
ngc6219	16.772919	9.037861
ngc6220	16.787022	-0.275472
ngc6221	16.879467	-59.218611
ngc6222,ngc6259	17.012611	-44.654972
ngc6223	16.717864	61.578917
ngc6224	16.80515	6.312222
ngc6225	16.805994	6.222778
ngc6227	16.859367	-41.230528
ngc6228	16.800739	26.213556
ngc6229	16.783017	47.527806
ngc6230	16.84575	4.605
ngc6231	16.903033	-41.82425
ngc6232	16.722289	70.632528
ngc6233	16.837694	23.579833
ngc6234	16.865928	4.383528
ngc6235	16.890378	-22.177444
ngc6236	16.742958	70.780222
ngc6237	16.735428	70.634806
ngc6238	16.787953	62.147028
ngc6239	16.834717	42.739694
ngc6241	16.836375	45.420611
ngc6242	16.925956	-39.460944
ngc6243	16.873969	23.332583
ngc6244	16.801086	62.200444
ngc6245	16.756244	70.804583
ngc6246	16.831311	55.542056
ngc6246a	16.837217	55.384611
ngc6248	16.772775	70.358806
ngc6249	16.961528	-44.811889
ngc6250	16.965575	-45.936639
ngc6251	16.542214	82.537889
ngc6252	16.544603	82.576778
ngc6253	16.984758	-52.708806
m10,ngc6254	16.952497	-4.099333
ngc6255	16.913319	36.501111
ngc6256	16.992414	-37.121417
ngc6257	16.934308	39.6455
ngc6258	16.874942	60.514528
ngc6260	16.864058	63.714583
ngc6261	16.941811	27.9775
ngc6262	16.978556	57.098389
ngc6263	16.945333	27.822083
ngc6264	16.954481	27.849611
ngc6265	16.958083	27.844222
m62,ngc6266	17.020167	-30.112361
ngc6267	16.969072	22.985111
ngc6268	17.036219	-39.728222
ngc6269	16.966136	27.854333
ngc6270	16.978903	27.859111
ngc6271	16.980769	27.964639
ngc6272	16.98285	27.930917
m19,ngc6273	17.0438	-26.267944
ngc6274	16.989144	29.943833
ngc6275	16.925936	63.242194
ngc6277	17.013581	23.039361
ngc6278	17.013981	23.011028
ngc6279	16.983731	47.237167
ngc6280	17.032636	6.66575
ngc6281	17.078139	-37.985222
ngc6282	17.013086	29.820611
ngc6283	16.990714	49.921972
ngc6284	17.074653	-24.764333
ngc6285	16.973336	58.955972
ngc6286	16.975383	58.93625
ngc6287	17.085928	-22.708
ngc6288	16.956792	68.457028
ngc6289	16.962497	68.514722
ngc6290	17.015675	58.9705
ngc6291	17.015533	58.937556
ngc6292	17.050964	61.043889
ngc6293	17.169558	-26.58175
ngc6294	17.171175	-26.574556
ngc6295	17.054264	60.33775
ngc6296	17.145686	3.894083
ngc6297,ngc6298	17.060153	62.025611
ngc6299	17.084558	62.457833
ngc6300	17.283186	-62.820556
bugnebula,butterflynebula,ngc6302	17.229064	-37.103139
ngc6303	17.084103	68.827583
ngc6304	17.242364	-29.462278
ngc6305	17.300256	-59.172083
ngc6306	17.126939	60.728889
ngc6307	17.127908	60.750778
ngc6308	17.199919	23.379944
boxnebula,ngc6309	17.234528	-12.910556
ngc6310	17.132631	60.990167
ngc6311	17.178769	41.651111
ngc6312	17.180044	42.287694
ngc6313	17.172444	48.33175
ngc6314	17.210753	23.270056
ngc6315	17.212819	23.223556
ngc6316	17.277058	-28.140028
ngc6317	17.149864	62.898
ngc6318	17.269886	-39.424972
ngc6319	17.162244	62.973056
ngc6320	17.215483	40.2665
ngc6321	17.240061	20.313917
ngc6322	17.307164	-42.934028
ngc6323	17.221689	43.782444
ngc6324	17.090367	75.407028
ngc6325	17.299797	-23.766028
ngc6326	17.346211	-51.754389
ngc6327	17.233969	43.649472
ngc6328	17.394731	-65.010167
ngc6329	17.237508	43.684694
ngc6330	17.262339	29.404306
ngc6331	17.059992	78.629
ngc6332	17.250806	43.660194
m9,ngc6333	17.319939	-18.51625
ngc6334	17.347139	-36.102722
ngc6335	17.325533	-30.164167
ngc6336	17.271269	43.820472
ngc6337	17.371003	-38.483722
ngc6338	17.256386	57.411194
ngc6339	17.285139	40.844972
ngc6340	17.173569	72.304444
m92,ngc6341	17.285353	43.136528
ngc6342	17.352817	-19.587417
ngc6343	17.287853	41.052722
ngc6344	17.288375	42.434194
ngc6345	17.256744	57.350306
ngc6346	17.256803	57.322528
ngc6348	17.305886	41.647611
ngc6349	17.318486	36.060917
ngc6350	17.311736	41.694333
ngc6351	17.319833	36.060556
ngc6352	17.424767	-48.422694
ngc6353	17.353464	15.688556
ngc6354	17.409522	-38.541611
ngc6355	17.399625	-26.353417
ngc6356	17.393053	-17.813028
ngc6357,thewarandpeacenebula	17.412103	-34.201333
ngc6358	17.314725	52.615278
ngc6359	17.298053	61.780806
ngc6360	17.407672	-29.871583
ngc6361	17.311414	60.608167
ngc6362	17.5319	-67.047861
ngc6364	17.407592	29.390167
ngc6365	17.378806	62.17
ngc6365a	17.378836	62.166083
ngc6365b	17.378758	62.173722
ngc6366	17.462314	-5.076639
ngc6367	17.419169	37.759889
ngc6368	17.453206	11.543611
littleghostnebula,ngc6369	17.489028	-23.759444
ngc6370	17.390328	56.974528
ngc6371	17.455719	26.505056
ngc6372	17.458847	26.475139
ngc6373	17.402247	58.995083
ngc6374,ngc6383	17.578483	-32.581361
ngc6375	17.489414	16.206667
ngc6376	17.421994	58.817444
ngc6377	17.423114	58.82275
ngc6378	17.511661	6.282278
ngc6379	17.509697	16.28875
ngc6380	17.574561	-39.069667
ngc6381	17.454681	60.014056
ngc6382	17.465328	56.868722
ngc6384	17.540083	7.060278
ngc6385	17.467058	57.521806
ngc6386	17.48105	52.723361
ngc6387	17.473286	57.545389
ngc6388	17.604842	-44.735611
ngc6389	17.544381	16.401778
ngc6390	17.474469	60.094167
ngc6391	17.480275	58.850889
ngc6392	17.725103	-69.785194
ngc6393	17.502347	59.531806
ngc6394	17.50595	59.639889
ngc6395	17.442019	71.096278
ngc6396	17.626761	-35.025861
ngc6397	17.678156	-53.673694
ngc6398	17.71215	-61.694278
ngc6399	17.530639	59.615528
ngc6400	17.670222	-36.947722
ngc6401	17.643592	-23.908778
m14,ngc6402	17.626711	-3.245917
ngc6403	17.723211	-61.682111
ngc6404	17.660378	-33.246722
butterflycluster,m6,ngc6405	17.672431	-32.254167
ngc6406	17.638625	18.833056
ngc6407	17.749358	-60.739806
ngc6408	17.646489	18.877861
ngc6409	17.609833	50.765889
ngc6410	17.589022	60.793056
ngc6411	17.592458	60.813389
ngc6412	17.493753	75.704417
ngc6413	17.677978	12.623944
ngc6414	17.510239	74.376139
ngc6415	17.739042	-35.071028
ngc6416	17.738886	-32.361
ngc6417	17.696617	23.672194
ngc6418	17.635922	58.714917
ngc6419	17.601639	68.155778
ngc6420	17.604528	68.052361
ngc6421	17.762281	-33.692639
ngc6422	17.608336	68.058611
ngc6423	17.614814	68.171472
ngc6424	17.603353	69.988889
ngc6425	17.7838	-31.529389
ngc6426	17.748531	3.170139
ngc6427,ngc6431	17.727386	25.493917
ngc6428	17.731336	25.554778
ngc6429	17.734819	25.350722
ngc6430	17.753964	18.138944
ngc6432	17.789558	-24.887472
ngc6433	17.732281	36.800111
ngc6434	17.613561	72.088972
ngc6435	17.669744	62.64175
ngc6436	17.687011	60.449694
ngc6437	17.805867	-35.366194
ngc6438	18.371522	-85.402056
ngc6438a	18.376525	-85.406333
ngc6439	17.8055	-16.478889
ngc6440	17.814631	-20.359583
ngc6441	17.8369	-37.051083
ngc6442	17.780928	20.761083
ngc6443	17.742736	48.114056
ngc6444	17.826439	-34.819667
littlegem,ngc6445	17.82085	-20.0095
ngc6446	17.768753	35.569389
ngc6447	17.771453	35.571972
ngc6448	17.728556	53.546111
ngc6449	17.729539	56.804139
ngc6450	17.792322	18.575222
ngc6451	17.844622	-30.211611
ngc6452	17.799592	20.837806
ngc6453	17.847697	-34.599889
ngc6454	17.749058	55.704778
ngc6455	17.85225	-35.337806
ngc6456	17.708847	67.592306
ngc6457	17.714678	66.476
ngc6458	17.819725	20.804278
ngc6459	17.763108	55.77675
ngc6460	17.8251	20.763667
ngc6461	17.665697	74.034222
ngc6462	17.746906	61.910583
ngc6463	17.7262	67.6035
ngc6464	17.763203	60.897472
ngc6465	17.882106	-25.397694
ngc6466	17.80225	51.399222
ngc6467,ngc6468	17.844489	17.537778
ngc6469	17.886703	-22.275111
ngc6470	17.737464	67.619389
ngc6471	17.737667	67.591944
ngc6472	17.734194	67.630333
ngc6473	17.766067	57.257111
ngc6474	17.784878	57.301167
m7,ngc6475,ptolemyscluster	17.89755	-34.792833
ngc6476	17.900558	-29.144167
ngc6477	17.741672	67.610583
ngc6478	17.810653	51.15725
ngc6479	17.805997	54.149
ngc6480	17.907233	-30.452056
ngc6481	17.880253	4.167833
ngc6482	17.863558	23.071944
ngc6483	17.991892	-63.668722
ngc6484	17.86305	24.483472
ngc6485	17.86465	31.461778
ngc6486	17.876472	29.818
ngc6487	17.878292	29.838639
ngc6488	17.822492	62.222917
ngc6489	17.833697	60.092222
ngc6490	17.908464	18.375833
ngc6491	17.833528	61.531778
ngc6492	18.046764	-66.430639
ngc6493	17.839628	61.559417
m23,ngc6494	17.951325	-18.985333
ngc6495	17.9141	18.326917
ngc6496	17.984361	-44.266306
ngc6497,ngc6498	17.854992	59.470889
ngc6499	17.922225	18.35975
ngc6500	17.933272	18.33825
ngc6501	17.934372	18.373083
ngc6502	18.070478	-65.409944
ngc6503	17.824008	70.144361
ngc6504	17.934919	33.208389
ngc6505	17.852067	65.530778
ngc6506	17.998192	-24.685333
ngc6507	17.997442	-17.450278
ngc6508	17.829567	72.021111
ngc6509	17.990353	6.287028
ngc6510,ngc6511	17.910917	60.817917
ngc6512	17.913975	62.645083
ngc6513	17.992925	24.880528
lbn27,m20,ngc6514,trifidnebula	18.045031	-22.971889
ngc6515	17.956997	50.728111
ngc6516	17.921328	62.669861
ngc6517	18.030664	-8.9595
ngc6518	17.995483	28.866667
ngc6519	18.055592	-29.80425
ngc6520	18.056706	-27.886111
ngc6521	17.930122	62.61225
ngc6522	18.059464	-30.033972
lagoonnebula,lbn25,m8,ngc6523,ngc6533	18.061464	-24.380167
ngc6524	17.987419	45.887083
ngc6525	18.034653	11.038333
ngc6526	18.068375	-24.441889
ngc6527	18.029536	19.728722
ngc6528	18.080447	-30.055778
ngc6529	18.09135	-36.295389
ngc6530	18.075286	-24.358056
m21,ngc6531	18.070403	-22.490056
ngc6532	17.987208	56.231778
ngc6534	17.935711	64.283694
ngc6535	18.064081	-0.296917
ngc6536	17.954542	64.938083
ngc6537,redspidernebula	18.086972	-19.842972
ngc6538	17.904614	73.423944
ngc6539	18.080486	-7.585861
ngc6540	18.102208	-27.762806
ngc6541	18.133981	-43.715889
ngc6542	17.994061	61.359389
catseyenebula,ngc6543	17.975942	66.633194
ngc6544	18.122222	-24.998361
ngc6545	18.204103	-63.776139
ngc6546	18.122931	-23.296222
ngc6547	18.086117	25.232611
ngc6548	18.099789	18.58725
ngc6549,ngc6550	18.097083	18.538028
ngc6551	18.149906	-29.557667
ngc6552	18.002008	66.615111
ngc6553	18.154856	-25.907861
ngc6554	18.156661	-18.378694
ngc6555	18.130325	17.604889
ngc6556	18.165997	-27.524806
ngc6557	18.356894	-76.582972
ngc6558	18.171772	-31.763472
lbn28,ngc6559	18.165792	-24.106389
ngc6560	18.087217	46.881583
ngc6561	18.175239	-16.725667
ngc6562	18.083586	56.263111
ngc6563	18.200694	-33.868333
ngc6564	18.150658	17.394639
ngc6565	18.197944	-28.178333
ngc6566	18.116853	52.260111
ngc6567	18.229222	-19.075833
ngc6568	18.212292	-21.628028
ngc6569	18.227408	-31.827667
ngc6570	18.185361	14.093083
ngc6571	18.180378	21.2385
ngc6572	18.201725	6.853722
ngc6573	18.239717	-22.174361
ngc6574,ngc6610	18.197564	14.981778
ngc6575	18.182636	31.116194
ngc6576	18.196672	21.42825
ngc6577	18.200342	21.463389
ngc6578	18.27125	-20.450917
ngc6579	18.208836	21.420694
ngc6580	18.209361	21.426139
ngc6582	18.184306	49.910556
ngc6583	18.263592	-22.137639
ngc6584	18.310458	-52.215167
ngc6585	18.206053	39.633
ngc6586	18.227361	21.090083
ngc6587	18.230803	18.825194
ngc6588	18.349683	-63.809972
ngc6591	18.234417	21.063889
ngc6592	18.164078	61.421972
ngc6593	18.234319	22.283917
ngc6594	18.1682	61.133472
ngc6596	18.292703	-16.650444
ngc6597	18.187069	61.180667
ngc6598	18.148889	69.067889
ngc6599,ngc6600	18.261939	24.912389
ngc6601	18.195653	61.453306
ngc6602	18.276192	25.044028
ngc6603	18.307492	-18.406056
ngc6604	18.300822	-12.243111
ngc6605	18.272689	-15.015194
ngc6606	18.244886	43.268639
ngc6607	18.204094	61.332917
ngc6608	18.208022	61.298167
ngc6609	18.209325	61.331917
lbn67,m16,ngc6611	18.313381	-13.807222
ngc6612	18.269681	36.078556
m18,ngc6613	18.332914	-17.101972
ngc6614	18.418669	-63.248361
ngc6615	18.309297	13.265028
ngc6616	18.294744	22.238444
ngc6617	18.234033	61.319556
checkmarknebula,lbn60,lobsternebula,m17,ngc6618,omeganebula,swannebula	18.346419	-16.171528
ngc6619	18.315428	23.655611
ngc6620	18.381708	-26.821694
ngc6621	18.215364	68.363444
ngc6622	18.216611	68.353889
ngc6623	18.328583	23.705556
ngc6624	18.394603	-30.361278
ngc6625	18.379806	-11.955
m28,ngc6626	18.409136	-24.869833
ngc6627	18.377478	15.698
ngc6628	18.372753	23.478556
ngc6629	18.428461	-23.202889
ngc6630	18.543094	-63.29325
ngc6631	18.453156	-12.031222
ngc6632	18.417525	27.535306
ngc6633	18.454231	6.508222
m69,ngc6634,ngc6637	18.523119	-32.347972
ngc6635	18.460308	14.819056
ngc6636	18.367639	66.620222
ngc6638	18.515625	-25.496417
ngc6639	18.516472	-13.155833
ngc6640	18.468964	34.302667
ngc6641	18.482603	22.903
ngc6642	18.531728	-23.476139
ngc6643	18.329558	74.568361
ngc6644	18.542981	-25.129361
ngc6645	18.543861	-16.883889
ngc6646	18.494094	39.865139
ngc6647	18.547039	-17.228667
ngc6648	18.427167	64.976167
ngc6649	18.557767	-10.402806
ngc6650	18.424442	68.005833
ngc6651	18.405475	71.601917
ngc6652	18.596042	-32.990306
ngc6653	18.743992	-73.263417
ngc6654	18.402103	73.183222
ngc6654a	18.656928	73.57975
ngc6655	18.57525	-5.920861
m22,ngc6656	18.606722	-23.903417
ngc6657	18.550406	34.060472
ngc6658	18.565458	22.888278
ngc6659	18.566647	23.594889
ngc6660,ngc6661	18.576853	22.909667
ngc6662	18.569772	32.064583
ngc6663	18.559356	40.048944
ngc6664	18.609264	-8.22075
ngc6665	18.575003	30.720556
ngc6666	18.579147	33.587639
ngc6667,ngc6668,ngc6678	18.511053	67.987028
ngc6669	18.620858	22.195722
ngc6670	18.559847	59.888806
ngc6670a	18.560478	59.889667
ngc6670b	18.559469	59.888222
ngc6671	18.623933	26.417194
ngc6672	18.603997	42.947639
ngc6673	18.751756	-62.297222
ngc6674	18.642742	25.375139
ngc6675	18.624022	40.057722
ngc6676	18.552767	66.959056
ngc6677	18.560036	67.11075
ngc6680	18.662214	22.316417
m70,ngc6681	18.720178	-32.291889
ngc6682	18.660378	-4.813694
ngc6683	18.703881	-6.21225
ngc6684	18.816078	-65.173444
ngc6684a	18.873003	-64.831472
ngc6685	18.666289	39.981778
ngc6686	18.668617	40.137639
ngc6687	18.622808	59.642972
ngc6688	18.677814	36.289639
ngc6689,ngc6690	18.580625	70.523917
ngc6691	18.653403	55.641806
ngc6692,ngc6693	18.694861	34.843611
m26,ngc6694	18.755183	-9.383611
ngc6695	18.711872	40.366889
ngc6696	18.668067	59.333972
ngc6697	18.754156	25.512583
ngc6698	18.801392	-25.477167
ngc6699	18.867233	-57.32075
ngc6700	18.767886	32.279611
ngc6701	18.720128	60.653333
ngc6702	18.782661	45.705667
ngc6703	18.788564	45.550639
ngc6704	18.846047	-5.205417
amasdelecudesobieski,m11,ngc6705,wildduckcluster	18.851664	-6.270028
ngc6706	18.947511	-63.166222
ngc6707	18.922794	-53.818444
ngc6708	18.926567	-53.723444
ngc6709	18.855261	10.31875
ngc6710	18.842819	26.838389
ngc6711	18.816911	47.658111
ngc6712	18.884692	-8.705472
ngc6713	18.845711	33.959778
ngc6714	18.780556	66.745
m54,ngc6715	18.917575	-30.4785
ngc6716	18.909547	-19.901083
ngc6717	18.918344	-22.701611
ngc6718	19.024619	-66.110194
ngc6719	19.052081	-68.588361
m57,ngc6720,ringnebula	18.893058	33.028583
ngc6721	19.014114	-57.759444
ngc6722	19.061214	-64.894472
ngc6723	18.992542	-36.631472
ngc6724	18.946356	10.428556
ngc6725	19.032394	-53.863083
ngc6726	19.027583	-36.891306
ngc6727	19.028408	-36.87625
ngc6728	18.979178	-8.966
ngc6729	19.032056	-36.957639
ngc6730	19.126014	-68.912806
ngc6731	18.953742	43.076778
ngc6732	18.940006	52.377611
ngc6733	19.102953	-62.196917
ngc6734	19.120647	-65.461861
ngc6735	19.010378	-0.475389
ngc6736	19.124792	-65.428611
ngc6737	19.038186	-18.546972
ngc6738	19.022656	11.615611
ngc6739	19.130211	-61.368111
ngc6740	19.014031	28.771222
ngc6741,phantomstreaknebula	19.043611	-0.449389
ngc6742	18.988861	48.465278
ngc6743	19.022408	29.277472
ngc6744	19.162806	-63.857528
ngc6744a	19.145489	-63.7305
ngc6745	19.02825	40.753056
ngc6746	19.172781	-61.970167
ngc6747	18.922681	72.771528
ngc6748,ngc6751	19.098764	-5.992306
ngc6749	19.087667	1.900611
ngc6750	19.010031	59.16675
ngc6752,ngc6777	19.18105	-59.981861
ngc6753	19.1899	-57.049556
ngc6754	19.190478	-50.641806
ngc6755	19.130292	4.266417
ngc6756	19.145158	4.705778
ngc6757	19.084272	55.715167
ngc6758	19.231206	-56.309944
ngc6759	19.115789	50.344222
ngc6760	19.186683	1.030472
ngc6761	19.251333	-50.656833
ngc6762,ngc6763	19.093633	63.934028
ngc6764	19.137881	50.933222
ngc6765	19.185139	30.545556
ngc6766,ngc6884	20.17325	46.460833
ngc6767	19.192753	37.725444
ngc6768	19.275722	-40.209167
ngc6769	19.3063	-60.501083
ngc6770	19.310367	-60.496472
ngc6771	19.310975	-60.546
ngc6772	19.243417	-2.706806
ngc6773	19.252347	4.856556
ngc6774	19.271194	-16.260694
ngc6775	19.278572	-0.933361
ngc6776	19.421986	-63.860167
ngc6776a	19.418161	-63.683444
ngc6778,ngc6785	19.306903	-1.596361
m56,ngc6779	19.276531	30.1845
ngc6780	19.3808	-55.775833
ngc6781	19.30785	6.539722
ngc6782	19.399417	-59.922472
ngc6783	19.279894	46.017222
ngc6784	19.443331	-65.617694
ngc6784a	19.441994	-65.626111
ngc6786	19.181642	73.410167
ngc6787	19.269606	60.417528
ngc6788	19.447153	-54.951306
ngc6789	19.278378	63.971472
ngc6790	19.382472	1.513333
ngc6791	19.348117	37.771889
ngc6792	19.349281	43.1325
ngc6793	19.387331	22.141028
ngc6794	19.467744	-38.91875
ngc6795	19.43945	3.514361
ngc6796	19.358575	61.144889
ngc6797	19.483542	-25.666556
ngc6799	19.537925	-55.907917
ngc6800	19.452133	25.140472
ngc6801	19.459947	54.372889
ngc6802	19.509733	20.260972
ngc6803	19.521236	10.056028
ngc6804	19.526497	9.225167
ngc6805	19.612697	-37.554361
ngc6806	19.618069	-42.296278
ngc6807	19.575972	5.684167
ngc6808	19.731667	-70.633389
m55,ngc6809	19.6665	-30.962083
ngc6810	19.726181	-58.655583
ngc6811	19.621642	46.388833
ngc6812	19.756728	-55.346806
ngc6813	19.6729	27.309556
ngc6814	19.711289	-10.3235
ngc6815	19.678975	26.759
ngc6816	19.733953	-28.400833
ngc6817	19.622889	62.383056
littlegemnebula,ngc6818	19.732703	-14.153167
foxheadcluster,ngc6819	19.688358	40.18675
ngc6820	19.707783	23.088083
ngc6821	19.740017	-6.833444
lbn135,ngc6823	19.719414	23.299944
ngc6824	19.727972	56.109472
ngc6825	19.698556	64.073056
blinkingplanetary,ngc6826	19.746697	50.525028
ngc6827	19.814844	21.215056
ngc6828	19.838225	7.902556
ngc6829	19.785433	59.907083
ngc6830	19.849883	23.100139
ngc6831	19.79925	59.892528
ngc6832	19.804239	59.421167
ngc6833	19.829611	48.961111
ngc6834	19.870156	29.408167
ngc6835	19.909153	-12.567583
ngc6836	19.911128	-12.687944
ngc6837	19.885731	11.699
m71,ngc6838	19.896142	18.778389
ngc6839	19.9	18.003333
ngc6840	19.921181	12.114611
ngc6841	19.963628	-31.810694
ngc6842	19.917294	29.289167
ngc6843	19.935061	12.163833
ngc6844	20.047258	-65.229861
ngc6845	20.016189	-47.069972
ngc6845a	20.016228	-47.07025
ngc6845b	20.018139	-47.059083
ngc6845c	20.015781	-47.084222
ngc6845d	20.014886	-47.095222
ngc6846	19.941144	32.349694
lbn151,ngc6847	19.943839	30.212917
ngc6848	20.046458	-56.090306
ngc6849	20.104339	-40.198306
ngc6850	20.058361	-54.844778
ngc6851	20.059547	-48.2845
ngc6851a	20.096808	-47.97825
ngc6851b	20.094428	-47.979056
ngc6852	20.010878	1.728111
dumbbellnebula,m27,ngc6853	19.993439	22.721028
ngc6854	20.094111	-54.375611
ngc6855	20.113864	-56.389917
ngc6856	19.988092	56.130889
ngc6857	20.030036	33.525917
ngc6858	20.049831	11.259417
ngc6859	20.063753	0.444639
ngc6860	20.146358	-61.100194
ngc6861b	20.101508	-48.474444
ngc6861c	20.111411	-48.649778
ngc6861d	20.138744	-48.211417
ngc6861e	20.183756	-48.690583
ngc6861f	20.186611	-48.275833
ngc6862	20.148494	-56.39175
ngc6863	20.085367	-3.555139
m75,ngc6864	20.101344	-21.922222
ngc6865	20.099022	-9.040917
ngc6866	20.065328	44.159111
ngc6867	20.174906	-54.78325
ngc6868	20.165019	-48.379556
ngc6869	20.011781	66.227528
ngc6870	20.169683	-48.287083
ngc6871	20.099844	35.77725
ngc6872	20.282378	-70.767944
ngc6873	20.120525	21.10225
ngc6874	20.125856	38.246111
ngc6875	20.220131	-46.161639
ngc6875a	20.19885	-46.144083
ngc6876	20.305319	-70.858806
ngc6877	20.310056	-70.853056
ngc6878	20.231456	-44.52675
ngc6878a	20.226667	-44.816167
ngc6879	20.174056	16.922806
ngc6880	20.324897	-70.859861
ngc6881	20.18125	37.411389
ngc6882,ngc6885	20.19885	26.488806
ngc6883	20.188819	35.832194
ngc6886	20.211917	19.989722
ngc6887	20.288136	-52.79675
crescentnebula,lbn203,ngc6888	20.201819	38.354944
ngc6889	20.314786	-53.957083
ngc6890	20.305028	-44.806722
ngc6891	20.252456	12.704361
ngc6892	20.282567	18.019667
ngc6893	20.347122	-48.239083
ngc6894	20.273347	30.565083
ngc6895	20.275656	50.240472
ngc6896	20.300994	30.640056
ngc6897	20.350353	-12.254694
ngc6898	20.352231	-12.358889
ngc6899	20.406178	-50.433944
ngc6900	20.359753	-2.569222
ngc6902a	20.383267	-44.271528
ngc6902b	20.385292	-43.868611
ngc6903	20.395794	-19.325417
ngc6904	20.363375	25.7415
blueflashnebula,ngc6905	20.373053	20.104528
ngc6906	20.392753	6.443667
ngc6907	20.418508	-24.809167
ngc6908	20.419158	-24.801139
ngc6909	20.460803	-47.027028
ngc6910	20.386681	40.778611
ngc6911	20.327314	66.728333
ngc6912	20.4478	-18.617278
m29,ngc6913	20.399381	38.507667
lbn274,ngc6914	20.412028	42.482639
ngc6915	20.462794	-3.077056
ngc6916	20.392522	58.344056
ngc6917	20.457878	8.098083
ngc6918	20.513089	-47.473722
ngc6919	20.527256	-44.216417
ngc6920	20.732611	-80.000833
ngc6921	20.474683	25.723417
ngc6922	20.498028	-2.191194
ngc6924	20.555342	-25.474444
ngc6926	20.551697	-2.0275
ngc6927	20.543947	9.916389
ngc6927a	20.543525	9.883917
ngc6929	20.556022	-2.037194
ngc6930	20.549667	9.874444
ngc6931	20.561486	-11.368861
ngc6932	20.702383	-73.619361
ngc6933	20.560606	7.387333
ngc6934	20.569858	7.404111
ngc6935	20.63895	-52.110444
ngc6936	20.598972	-25.279972
ngc6937	20.646064	-52.14325
ngc6938	20.578469	22.214583
ngc6939	20.525036	60.662083
ngc6940	20.574081	28.282722
ngc6941	20.606519	-4.61875
ngc6942	20.677181	-54.303056
ngc6943	20.742706	-68.747722
ngc6944	20.639961	6.996444
ngc6944a	20.636475	6.902667
ngc6945	20.650172	-4.972583
fireworksgalaxy,ngc6946	20.5812	60.153917
ngc6947	20.687533	-32.486417
ngc6948	20.724761	-53.356722
ngc6949	20.585256	64.802806
ngc6950	20.684883	16.622222
ngc6951,ngc6952	20.620581	66.105639
ngc6953	20.629506	65.764861
ngc6954	20.734217	3.209444
ngc6955	20.738328	2.594833
ngc6956	20.731586	12.511917
ngc6957	20.746544	2.581222
ngc6958	20.811831	-37.997417
ngc6959	20.785344	0.430194
filamentarynebula,lbn191,ngc6960,veilnebula,westernveil	20.766161	30.595139
ngc6961	20.786253	0.363278
ngc6962	20.788628	0.320806
ngc6963	20.788742	0.510639
ngc6964	20.790083	0.300833
ngc6966	20.790767	0.367694
ngc6967	20.792806	0.411611
ngc6968	20.809022	-8.360306
ngc6969	20.807675	7.739972
ngc6970	20.869294	-48.777778
ngc6971	20.823267	5.995583
ngc6972	20.833039	9.899139
ngc6973	20.868311	-5.895194
ngc6974	20.8512	31.828111
ngc6975,ngc6976	20.873897	-5.772306
ngc6977	20.874919	-5.746111
ngc6978	20.876508	-5.711139
ngc6979	20.841114	32.025889
ngc6980	20.880261	-5.837889
m72,ngc6981	20.891086	-12.537056
ngc6982	20.955106	-51.862278
ngc6983	20.945397	-43.986028
ngc6984	20.964994	-51.870833
ngc6985	20.750828	-11.104194
ngc6985a	20.750353	-11.107667
ngc6986	20.94185	-18.566556
ngc6987	20.969544	-48.630306
ngc6988	20.930267	10.507861
ngc6989	20.901922	45.239278
ngc6990	20.999144	-55.561972
ngc6991	20.914444	47.461667
easternveil,networknebula,ngc6992	20.938631	31.74275
ngc6993	20.898347	-25.472528
m73,ngc6994	20.982214	-12.6355
ngc6995	20.952989	31.235167
ngc6996	20.941669	45.473028
ngc6997	20.944292	44.6315
ngc6998	21.027133	-28.031917
ngc6999	21.033206	-28.058917
lbn373,ngc7000,northamericanebula	20.988094	44.528778
ngc7001	21.018819	-0.195167
ngc7002	21.062444	-49.02975
ngc7003	21.011783	17.804889
ngc7004	21.067272	-49.11425
ngc7005	21.032681	-12.882611
ngc7006	21.024792	16.187528
ngc7007	21.091089	-52.551972
ngc7008	21.009111	54.543194
ngc7009,saturnnebula	21.069664	-11.36325
ngc7011	21.030383	47.354306
ngc7012	21.112644	-44.814722
ngc7013	21.059328	29.897472
ngc7014	21.131158	-47.179
ngc7015	21.093717	11.414167
ngc7016	21.121189	-25.468944
ngc7017	21.122369	-25.486861
ngc7018	21.123708	-25.42775
ngc7019	21.107147	-24.412667
ngc7020,ngc7021	21.188914	-64.025333
ngc7022	21.159789	-49.303667
irisnebula,lbn487,ngc7023	21.026561	68.169556
ngc7024	21.102253	41.484583
ngc7025	21.129817	16.335861
ngc7026	21.105133	47.852194
ngc7027	21.117092	42.236528
ngc7028	21.097233	18.468194
ngc7029	21.197792	-49.283722
ngc7030	21.187036	-20.485861
ngc7031	21.120153	50.875556
ngc7032	21.256356	-68.287889
ngc7033	21.160072	15.124889
ngc7034	21.160606	15.150667
ngc7035	21.179556	-23.135833
ngc7035a	21.179294	-23.135139
ngc7035b	21.179806	-23.137083
ngc7036	21.170108	15.376111
ngc7037	21.179367	33.728333
ngc7038	21.252086	-47.2205
ngc7039	21.179944	45.621806
ngc7040	21.22125	8.864972
ngc7041	21.275661	-48.363556
ngc7042	21.229406	13.574917
ngc7043	21.234492	13.626028
ngc7044	21.219281	42.496194
ngc7045	21.247239	4.506778
ngc7046	21.2489	2.834833
ngc7047	21.274347	-0.8265
ngc7048	21.237556	46.288611
ngc7049	21.31675	-48.562167
ngc7050	21.252375	36.17525
ngc7051	21.330925	-8.782944
ngc7052	21.309181	26.447028
ngc7053	21.352114	23.084806
ngc7054,ngc7080	21.500542	26.717806
ngc7055	21.325031	57.545611
ngc7057	21.416306	-42.460444
ngc7058	21.364883	50.819028
ngc7059	21.455964	-60.014583
ngc7060	21.43155	-42.411278
ngc7061	21.457458	-49.0635
ngc7062	21.390967	46.378528
ngc7063	21.406028	36.4875
ngc7064	21.484161	-52.767611
ngc7065	21.445142	-6.994917
ngc7065a	21.449403	-7.021528
ngc7066	21.437222	14.181944
ngc7067	21.406422	48.00925
ngc7068	21.442325	12.184306
ngc7069	21.468297	-1.646861
ngc7070	21.507042	-43.087111
ngc7070a	21.529803	-42.847667
ngc7071	21.444258	47.919583
ngc7072	21.510256	-43.153528
ngc7072a	21.507133	-43.202611
ngc7073	21.490561	-11.488139
ngc7074	21.494122	6.682556
ngc7075	21.525828	-38.617917
ngc7076	21.439861	62.8925
ngc7077	21.499892	2.414167
m15,ngc7078	21.49955	12.166833
ngc7079	21.543125	-44.067556
ngc7081	21.523367	2.491278
ngc7082	21.488261	47.126278
ngc7083	21.595747	-63.902833
ngc7084	21.542536	17.508528
ngc7085	21.540342	6.58125
ngc7086	21.507653	51.600528
ngc7087	21.575964	-40.818639
ngc7088	21.556144	-0.382611
m2,ngc7089	21.557503	-0.823306
ngc7090	21.608017	-54.557333
m39,ngc7092	21.530089	48.438167
ngc7093	21.572694	45.965
ngc7094	21.614714	12.788639
ngc7095	21.874011	-81.530833
ngc7097	21.670253	-42.539389
ngc7097a	21.677183	-42.480278
ngc7098	21.737811	-75.111333
m30,ngc7099	21.672783	-23.179083
ngc7100	21.651956	8.951528
ngc7101	21.659614	8.876944
ngc7103	21.664306	-22.473889
ngc7104	21.66755	-22.424806
ngc7105	21.694819	-10.6355
ngc7106	21.710164	-52.699528
ngc7107	21.707356	-44.790278
ngc7108,ngc7111	21.698264	-6.708833
ngc7109	21.699592	-34.445889
ngc7110	21.703375	-34.162222
ngc7112,ngc7113	21.7074	12.56925
ngc7114,schmidtsnovacygni	21.695564	42.841806
ngc7115	21.727369	-25.351611
ngc7116	21.711172	28.946583
ngc7117	21.763067	-48.420417
ngc7118	21.769372	-48.353806
ngc7119	21.770972	-46.518056
ngc7119a	21.771125	-46.516139
ngc7119b	21.770883	-46.518417
ngc7120	21.742561	-6.523167
ngc7121	21.747939	-3.619722
ngc7122	21.763283	-8.829611
ngc7123	21.846286	-70.334139
ngc7124	21.801497	-50.565222
ngc7125	21.821106	-60.713167
ngc7126	21.821703	-60.609222
ngc7127	21.728331	54.629972
ngc7128	21.732725	53.715139
lbn497,ngc7129	21.716397	66.112972
ngc7131	21.793364	-13.182611
ngc7132	21.787939	10.241167
ngc7133	21.74075	66.168417
ngc7134	21.815628	-12.973139
ngc7136	21.828647	-11.793306
ngc7137	21.803622	22.159583
ngc7138	21.816969	12.514222
ngc7139	21.769056	63.791944
ngc7140,ngc7141	21.870919	-55.569667
ngc7142	21.752642	65.774444
ngc7143	21.814908	29.954972
ngc7144	21.878453	-48.25375
ngc7145	21.888956	-47.882444
ngc7146	21.863158	3.017028
ngc7147	21.866231	3.071694
ngc7148	21.869019	3.341472
ngc7149	21.869911	3.301139
ngc7150	21.839997	49.756083
ngc7151	21.917817	-50.657889
ngc7152	21.899733	-29.289083
ngc7153	21.909836	-29.063611
ngc7154	21.922511	-34.814139
ngc7156	21.909342	2.943028
ngc7157	21.949083	-25.350528
ngc7158	21.957811	-11.592528
ngc7159	21.940447	13.562639
ngc7160	21.894519	62.603306
ngc7161	21.949414	2.916222
ngc7162	21.994203	-43.305972
ngc7162a	22.009931	-43.141722
ngc7163	21.989011	-31.883167
ngc7164	21.9399	1.363944
ngc7165	21.990583	-16.512333
ngc7166	22.009144	-43.389722
ngc7167	22.008511	-24.632611
ngc7168	22.035389	-51.743083
ngc7169	22.046844	-47.697833
ngc7170	22.023961	-5.432778
ngc7171	22.017225	-13.26975
ngc7172	22.033858	-31.869667
ngc7173	22.034219	-31.973694
ngc7174	22.035125	-31.992972
ngc7175	21.977731	54.806361
ngc7176	22.035678	-31.98975
ngc7177	22.011456	17.738056
ngc7178	22.040333	-35.790361
ngc7179	22.080367	-64.046833
ngc7180	22.038461	-20.54775
ngc7181	22.028747	-1.960556
ngc7182	22.031017	-2.196583
ngc7183	22.039339	-18.9165
ngc7184	22.044394	-20.812833
ngc7185	22.049097	-20.471278
ngc7186	22.018117	35.078833
ngc7187	22.045711	-32.802167
ngc7188	22.058056	-20.317972
ngc7189	22.054444	0.571111
ngc7190	22.051856	11.199306
ngc7191	22.114386	-64.634556
ngc7192	22.113933	-64.31625
ngc7193	22.050433	10.803833
ngc7194	22.058594	12.636778
ngc7195	22.058411	12.660833
ngc7196	22.098558	-50.119333
ngc7197	22.049458	41.059
ngc7198	22.087289	-0.648278
ngc7199	22.141622	-64.706139
ngc7200	22.119311	-49.995472
ngc7201	22.108869	-31.263
ngc7202	22.112011	-31.217889
ngc7203	22.112189	-31.162417
ngc7204	22.115056	-31.051389
ngc7204a	22.115	-31.050611
ngc7204b	22.11535	-31.053083
ngc7205	22.142858	-57.442583
ngc7205a	22.125558	-57.464028
ngc7206	22.094692	16.78525
ngc7207	22.096022	16.76775
ngc7208	22.140117	-29.051167
ngc7209	22.085511	46.483528
ngc7210,ngc7487	23.114039	28.179028
ngc7211	22.106075	-8.089972
ngc7212	22.117028	10.231111
ngc7213	22.154531	-47.166611
ngc7214	22.152133	-27.809472
ngc7215	22.142911	0.511694
ngc7216	22.209956	-68.661861
ngc7217	22.131219	31.359333
ngc7218	22.169919	-16.661
ngc7219	22.219172	-64.848972
ngc7220	22.191944	-22.952861
ngc7221	22.187569	-30.563167
ngc7222	22.181044	2.105806
ngc7223	22.169211	41.017278
ngc7224	22.193161	25.8645
ngc7225	22.218908	-26.148333
ngc7226	22.174136	55.398583
ngc7227	22.192036	38.721361
ngc7228	22.196833	38.699167
ngc7229	22.234228	-29.38275
ngc7230	22.236997	-17.074056
ngc7231	22.208367	45.328472
ngc7232	22.260556	-45.850083
ngc7232a	22.228178	-45.893722
ngc7232b	22.264569	-45.780639
ngc7233	22.263606	-45.846444
ngc7234,ngc7235	22.20695	57.271333
ngc7236	22.245831	13.846528
ngc7237	22.246356	13.840861
ngc7238	22.255697	22.519222
ngc7239	22.250389	-5.053333
ngc7240	22.256267	37.280667
ngc7241	22.263853	19.232361
ngc7242	22.26125	37.300556
ngc7243	22.252383	49.8975
ngc7244	22.274119	16.471444
ngc7245	22.253197	54.342556
ngc7247	22.294792	-23.731028
ngc7248	22.28165	40.502333
ngc7249	22.341944	-55.124861
ngc7250	22.304944	40.562389
ngc7251	22.340872	-15.773556
ngc7252	22.345764	-24.678278
ngc7253	22.324694	29.391667
ngc7253a	22.324364	29.395806
ngc7253b	22.325028	29.387778
ngc7254,ngc7256	22.376731	-21.737222
ngc7255	22.385556	-15.541417
ngc7257,ngc7260	22.376789	-4.12075
ngc7258	22.382797	-28.345139
ngc7259	22.384867	-28.954833
ngc7261	22.335108	58.051833
ngc7262	22.391261	-32.36425
ngc7263	22.362569	36.35
ngc7264	22.370494	36.387
ngc7265	22.374289	36.209611
ngc7266	22.399711	-4.073417
ngc7267	22.406058	-33.694083
ngc7268	22.428167	-31.200556
ngc7269	22.429619	-13.166389
ngc7270	22.396536	32.403028
ngc7271	22.399331	32.366861
ngc7272	22.408808	16.588167
ngc7273	22.402564	36.199833
ngc7274	22.403086	36.125861
ngc7275	22.404786	32.44625
ngc7276	22.403992	36.087556
ngc7277	22.436372	-31.14525
ngc7278	22.472892	-60.169833
ngc7279	22.453517	-35.140444
ngc7280	22.440994	16.148222
ngc7281	22.422494	57.821139
ngc7282	22.431628	40.314861
ngc7283	22.475761	17.470333
ngc7284	22.476647	-24.844139
ngc7285	22.477222	-24.840778
ngc7286	22.464033	29.095972
ngc7287	22.480194	-22.2025
ngc7287a	22.480136	-22.203361
ngc7287b	22.480192	-22.201778
ngc7288	22.470825	-2.884556
ngc7289	22.488958	-35.471972
ngc7290	22.474008	17.147444
ngc7291	22.474861	16.783139
ngc7292	22.473864	30.292306
helixnebula,ngc7293	22.494047	-20.837333
ngc7295,ngc7296	22.467456	52.289083
ngc7297	22.519522	-37.826444
ngc7298	22.514069	-14.18825
ngc7299	22.525864	-37.809556
ngc7301	22.509644	-17.573778
ngc7303	22.525786	30.955972
ngc7304	22.529028	30.979667
ngc7305	22.537206	11.712139
ngc7306	22.554575	-27.246611
ngc7307	22.564594	-40.932722
ngc7309	22.572386	-10.357
ngc7310	22.576919	-22.485083
ngc7311	22.568531	5.569889
ngc7312	22.576331	5.817361
ngc7313	22.592378	-26.101778
ngc7314	22.596164	-26.050472
ngc7315	22.592142	34.803389
ngc7316	22.598983	20.32225
ngc7317	22.597744	33.944889
ngc7318	22.599333	33.965556
ngc7318a	22.599097	33.965472
ngc7318b	22.599558	33.965917
ngc7319	22.600986	33.975722
ngc7320	22.600939	33.948111
ngc7320c	22.605658	33.984972
ngc7321	22.607783	21.621806
ngc7322,ngc7334	22.630961	-37.231194
ngc7323	22.614914	19.143861
ngc7324	22.616922	19.14625
ngc7325	22.613478	34.368028
ngc7326	22.614469	34.423111
ngc7327	22.609456	34.503611
ngc7328	22.6248	10.531583
ngc7329	22.673394	-66.478972
ngc7330	22.615606	38.548056
ngc7331	22.617781	34.415528
ngc7332	22.623483	23.798333
ngc7333	22.6199	34.437833
ngc7335	22.622053	34.44775
ngc7336	22.622761	34.48175
ngc7337	22.624061	34.374306
ngc7338	22.625367	34.414472
ngc7339	22.629789	23.786694
ngc7340	22.62895	34.41
ngc7341	22.651539	-22.666667
ngc7342	22.636986	35.498861
ngc7343	22.64385	34.071444
ngc7344	22.660069	-4.158972
ngc7345	22.645794	35.540583
ngc7346	22.659847	11.083333
ngc7347	22.665603	11.027556
ngc7348	22.676744	11.906222
ngc7349	22.687472	-21.7985
ngc7350	22.680156	12.006528
ngc7351	22.690817	-4.444722
ngc7352	22.662139	57.394361
ngc7353	22.703475	11.877306
ngc7354	22.672114	61.284833
ngc7355	22.725156	-36.865167
ngc7356	22.700653	30.708806
ngc7357	22.70665	30.171361
ngc7358	22.760122	-65.121833
ngc7359	22.746667	-23.688083
ngc7360	22.726097	4.151167
ngc7362	22.730356	8.705444
ngc7363	22.722197	34.0015
ngc7364	22.740103	-0.162083
ngc7365	22.752789	-19.952028
ngc7366	22.740731	10.781361
ngc7367	22.742903	3.646389
ngc7368	22.7588	-39.341833
ngc7369	22.73675	34.351222
ngc7370	22.760342	11.057806
ngc7371	22.767706	-11.001139
ngc7372	22.762778	11.130833
ngc7373	22.772058	3.210056
ngc7374	22.766931	10.853611
ngc7375	22.775567	21.083639
ngc7376	22.788161	3.645583
ngc7377	22.796528	-22.312111
ngc7378	22.796583	-11.816639
ngc7379	22.792486	40.238806
lbn511,ngc7380	22.789169	58.132417
ngc7381	22.835597	-19.725111
ngc7382	22.839978	-36.857306
ngc7383	22.826561	11.556389
ngc7384	22.828486	11.487444
ngc7385	22.831831	11.608556
ngc7386	22.833931	11.698361
ngc7387	22.838233	11.636722
ngc7388	22.839172	11.710944
ngc7389	22.837792	11.566194
ngc7390	22.838783	11.531028
ngc7391	22.843369	-1.544833
ngc7392	22.863539	-20.608083
ngc7393	22.860581	-5.557306
ngc7394	22.835467	52.180111
ngc7395	22.850814	37.087806
ngc7396	22.872956	1.092389
ngc7397	22.879639	1.132778
ngc7398	22.880353	1.201111
ngc7399	22.877572	-9.267778
ngc7400	22.905783	-45.347028
ngc7401	22.882933	1.142667
ngc7402	22.884578	1.144444
ngc7403	22.885111	1.482722
ngc7405	22.882547	12.593611
ngc7406	22.898956	-6.57925
ngc7407	22.889133	32.130667
ngc7408	22.932461	-63.694722
ngc7409	22.8967	20.210389
ngc7410	22.916931	-39.661333
ngc7411	22.9097	20.236167
ngc7412	22.929375	-42.642028
ngc7412a	22.9525	-42.804472
ngc7413	22.917528	13.220472
ngc7414	22.92345	13.248278
ngc7415	22.914894	20.261556
ngc7416	22.92825	-5.495333
ngc7417	22.963753	-65.038556
ngc7418	22.943378	-37.030083
ngc7418a	22.944792	-36.772722
ngc7419	22.905572	60.815528
ngc7420	22.925569	29.805
ngc7421	22.948425	-37.34725
ngc7422	22.936772	3.926778
ngc7423	22.919039	57.096917
ngc7424	22.955103	-41.070583
ngc7425	22.954317	-10.95
ngc7426	22.934128	36.361361
ngc7427	22.952756	8.505583
ngc7428	22.955425	-1.049
ngc7429	22.9335	59.973861
ngc7430	22.958256	8.794306
ngc7431	22.960747	26.164306
ngc7432	22.967206	13.1345
ngc7433	22.964364	26.162167
ngc7434	22.972625	-1.183944
ngc7435	22.965131	26.138861
ngc7436	22.965806	26.15
ngc7436a	22.965603	26.149972
ngc7436b	22.965983	26.149944
ngc7437	22.969461	14.3085
ngc7438	22.955658	54.309306
ngc7439	22.969433	29.228417
ngc7440	22.975706	35.802417
ngc7442	22.990708	15.548389
ngc7443	23.002458	-12.807889
ngc7444	23.002489	-12.834278
ngc7445	22.989567	39.107528
ngc7446	22.991389	39.082889
ngc7447	23.007244	-10.528
ngc7448	23.000997	15.980333
ngc7449	22.993789	39.145861
ngc7450	23.013283	-12.918528
ngc7451	23.01135	8.467917
ngc7452	23.013194	6.745528
ngc7453	23.023725	-6.3565
ngc7454	23.018475	16.388361
ngc7455	23.011381	7.303056
ngc7456	23.036228	-39.569389
ngc7457	23.016647	30.144944
ngc7458	23.024622	1.753389
ngc7459	23.016639	6.75
ngc7460	23.028586	2.263611
ngc7461	23.030092	15.582472
ngc7462	23.046247	-40.83525
ngc7463	23.031106	15.981861
ngc7464	23.031583	15.97375
ngc7465	23.033603	15.964778
ngc7466	23.034286	27.052639
ngc7467	23.040967	15.554083
ngc7468	23.049794	16.60525
ngc7469	23.054339	8.874
ngc7470	23.087239	-50.111583
ngc7471	23.06495	-22.906917
ngc7472,ngc7482	23.094058	3.05925
ngc7473	23.065858	30.160139
ngc7474	23.067897	20.067194
ngc7475	23.069694	20.081139
ngc7476	23.086631	-43.099361
ngc7477	23.077961	3.118
ngc7478	23.082392	2.577778
ngc7479	23.082403	12.322889
ngc7480	23.087117	2.549417
ngc7481	23.097672	-19.939667
ngc7483	23.096747	3.545111
ngc7484	23.118031	-36.275361
ngc7485	23.10135	34.107694
ngc7486	23.103606	34.1015
ngc7488	23.130264	0.940528
ngc7489	23.125753	22.998
ngc7490	23.123658	32.375056
ngc7491	23.134994	-5.966667
ngc7492	23.140744	-15.611472
ngc7493	23.142119	0.91
ngc7494	23.149606	-24.369583
ngc7495	23.149217	12.048028
ngc7496	23.163136	-43.427944
ngc7496a	23.206467	-43.778194
ngc7497	23.150947	18.177194
ngc7498	23.165611	-24.425056
ngc7499	23.172886	7.580667
ngc7500	23.174947	11.012306
ngc7501	23.175117	7.589028
ngc7502	23.172164	-21.737583
ngc7503	23.178411	7.567694
ngc7504	23.178103	14.386306
ngc7505	23.183514	13.631556
ngc7506	23.194717	-2.160028
ngc7507	23.202108	-28.539611
ngc7508	23.196997	12.940417
ngc7509	23.205947	14.609361
ngc7510	23.184383	60.570889
ngc7511	23.207303	13.726583
ngc7512	23.205814	31.125611
ngc7513	23.220564	-28.3575
ngc7514	23.207183	34.8815
ngc7515	23.213519	12.679278
ngc7516	23.214406	20.248417
ngc7517	23.220508	-2.100417
ngc7518	23.220203	6.321667
ngc7519	23.219789	10.772167
ngc7520	23.229133	-23.794194
ngc7521	23.226486	-1.7315
ngc7522	23.260111	-22.894861
ngc7523	23.226311	13.986806
ngc7524	23.229597	-1.730083
ngc7525	23.227878	14.022972
ngc7526	23.233981	-9.221639
ngc7527	23.228269	24.902278
ngc7528	23.238961	10.231444
ngc7529	23.234219	8.9925
ngc7530	23.236619	-2.779333
ngc7531	23.246806	-43.599944
ngc7532	23.239508	-2.728194
ngc7533	23.239467	-2.033722
ngc7534	23.240744	-2.69825
ngc7535	23.236881	13.581889
ngc7536	23.236994	13.426389
ngc7537	23.242917	4.498361
lbn542,ngc7538	23.227397	61.512389
ngc7539	23.241511	23.684833
ngc7540	23.243353	15.950306
ngc7541,ngc7581	23.245525	4.534361
ngc7542	23.244897	10.64325
ngc7543	23.242939	28.327222
ngc7544	23.249161	-2.199333
ngc7545	23.258917	-38.535583
ngc7546	23.251567	-2.32475
ngc7547	23.250944	18.973444
ngc7548	23.253086	25.281944
ngc7549	23.254786	19.041694
ngc7550	23.254447	18.961806
ngc7551	23.256119	15.941
ngc7553	23.259192	19.048167
ngc7554	23.261483	-2.378611
ngc7555	23.258569	12.572861
ngc7556	23.262353	-2.3815
ngc7556a	23.262147	-2.385556
ngc7557	23.261047	6.708333
ngc7558	23.260619	18.919694
ngc7559	23.262861	13.293889
ngc7559a	23.262775	13.296944
ngc7559b	23.262933	13.290278
ngc7560	23.264933	4.495861
ngc7561	23.26595	4.522722
ngc7562	23.265972	6.687528
ngc7562a	23.267072	6.652278
ngc7563	23.265536	13.196111
ngc7564	23.266997	7.348056
ngc7565	23.272169	-0.058611
ngc7566	23.277064	-2.330556
ngc7567	23.269522	15.850028
ngc7568,ngc7574	23.273575	24.497028
ngc7569	23.279042	8.905444
ngc7570	23.279075	13.483
ngc7571,ngc7597	23.308406	18.68875
ngc7572	23.280658	18.483167
ngc7573	23.273986	-22.154389
ngc7575	23.289131	5.660778
ngc7576	23.28965	-4.727861
ngc7577	23.288083	7.365417
ngc7578	23.286861	18.704444
ngc7578a	23.28665	18.701306
ngc7578b	23.2871	18.70825
ngc7579	23.294125	9.433306
ngc7580	23.293444	14.001194
ngc7582	23.306528	-42.370556
ngc7583,ngc7605	23.297992	7.379444
ngc7584	23.298056	9.433333
ngc7585	23.300372	-4.650306
ngc7586	23.298778	8.584083
ngc7587	23.299758	9.680194
ngc7588	23.299392	18.752167
ngc7589	23.304353	0.261167
ngc7590	23.315225	-42.239056
ngc7591	23.304522	6.585806
ngc7592	23.306167	-4.416944
ngc7592a	23.306056	-4.41575
ngc7592b	23.306275	-4.416139
ngc7592c	23.306147	-4.418889
ngc7593	23.299164	11.349167
ngc7595	23.308397	9.932417
ngc7598	23.309242	18.749361
ngc7600	23.314961	-7.580444
ngc7601	23.313069	9.233611
ngc7602	23.312092	18.698361
ngc7603	23.315728	0.243944
ngc7604	23.29775	7.429889
ngc7606	23.317994	-8.485083
ngc7608	23.320925	8.350139
ngc7609	23.325139	9.505278
ngc7610,ngc7616	23.328158	10.185
ngc7611	23.326833	8.06325
ngc7612	23.328944	8.576389
ngc7613,ngc7614	23.331044	0.198861
ngc7615	23.331789	8.399417
ngc7617	23.335825	8.165778
ngc7618	23.329783	42.852639
ngc7619	23.337369	8.20625
ngc7620	23.334911	24.221139
ngc7621	23.340172	8.366306
ngc7622	23.360703	-62.11775
ngc7623	23.341672	8.395806
ngc7624	23.339614	27.315694
ngc7625	23.341703	17.225556
ngc7626	23.345153	8.216972
ngc7627,ngc7641	23.375258	11.892556
ngc7628	23.348578	25.898556
ngc7629	23.355381	1.403139
ngc7630	23.354531	11.397333
ngc7631	23.357408	8.217639
ngc7633	23.38425	-67.653722
ngc7634	23.3616	8.886917
bubblenebula,lbn548,ngc7635	23.346	61.212361
ngc7636	23.375822	-29.280694
ngc7637	23.441017	-81.911583
ngc7640	23.368494	40.845417
ngc7642	23.3815	1.442778
ngc7643,ngc7644	23.380667	11.988833
ngc7645	23.396469	-29.388028
ngc7647	23.399286	16.777278
ngc7650	23.422625	-57.791361
ngc7651	23.407167	13.97
ngc7652	23.427064	-57.887389
ngc7653	23.413711	15.275583
m52,ngc7654	23.413444	61.593167
ngc7655	23.446094	-68.027528
ngc7656	23.408725	-19.059056
ngc7657	23.446531	-57.80575
ngc7658	23.440194	-39.221806
ngc7658a	23.440186	-39.215972
ngc7658b	23.440236	-39.226611
ngc7659	23.432133	14.209833
ngc7660	23.430183	27.029889
ngc7661	23.453969	-65.270417
copelandsbluesnowball,ngc7662	23.431639	42.534944
ngc7663	23.445894	-4.966667
ngc7664	23.444378	25.080139
ngc7665	23.454111	-9.387
ngc7666	23.456808	-4.186306
ngc7667	23.406417	-0.108056
ngc7668,ngc7669,ngc7670	23.456061	-0.191306
ngc7671	23.455372	12.467417
ngc7672	23.458733	12.385194
ngc7673	23.461394	23.589028
ngc7674	23.465756	8.779028
ngc7675	23.468311	8.768583
ngc7676	23.483811	-59.716667
ngc7677	23.468367	23.531389
ngc7678	23.474417	22.421194
ngc7679	23.479639	3.511472
ngc7680	23.476417	32.415722
ngc7681	23.481914	17.309639
ngc7682	23.484425	3.533333
ngc7683	23.484394	11.445167
ngc7684	23.5089	0.081056
ngc7685	23.509306	3.901583
ngc7686	23.50205	49.134111
ngc7687	23.515125	3.546611
ngc7688	23.518194	21.411528
ngc7689	23.554647	-54.094472
ngc7690	23.550711	-51.698361
ngc7691	23.540117	15.847833
ngc7692	23.546322	-5.596889
ngc7693	23.552919	-1.291861
ngc7694	23.554381	-2.702889
ngc7695	23.554167	-2.720194
ngc7696	23.563919	4.870806
ngc7698	23.567106	24.944611
ngc7699	23.574175	-2.899444
ngc7700	23.575081	-2.953667
ngc7701	23.575417	-2.854278
ngc7702	23.591356	-56.012278
ngc7703	23.579686	16.075778
ngc7704	23.583619	4.897528
ngc7705	23.584033	4.803806
ngc7706	23.586236	4.964194
ngc7707	23.580944	44.304056
ngc7708	23.583739	72.833167
ngc7709	23.590964	-16.705083
ngc7710	23.59615	-2.880917
ngc7711	23.594269	15.301972
ngc7712	23.597678	23.61875
ngc7713	23.604164	-37.938083
ngc7713a	23.618969	-37.714139
ngc7714	23.603917	2.155167
ngc7715	23.60615	2.156528
ngc7716	23.608736	0.297278
ngc7717	23.628797	-15.1185
ngc7718	23.634725	25.719722
ngc7719	23.634047	-22.974417
ngc7720	23.641497	27.031444
ngc7720a	23.641539	27.03475
ngc7721	23.646847	-6.517861
ngc7722	23.644778	15.954639
ngc7723	23.649189	-12.961083
ngc7724	23.651989	-12.224056
ngc7725	23.654106	-4.539389
ngc7726	23.653308	27.115333
ngc7727	23.664922	-12.292778
ngc7728	23.6669	27.133722
ngc7729	23.676014	29.188167
ngc7730	23.679431	-20.508806
ngc7731	23.691408	3.740028
ngc7732	23.692742	3.724944
ngc7733	23.709153	-65.9565
ngc7734	23.711925	-65.944639
ngc7735	23.704808	26.23175
ngc7736	23.707161	-19.452306
ngc7737	23.712892	27.052944
ngc7738	23.733906	0.516639
ngc7739	23.741689	0.320472
ngc7740	23.725633	27.311889
ngc7741	23.731769	26.075611
ngc7742	23.737703	10.767083
ngc7743	23.739206	9.934083
ngc7745	23.746053	25.908972
ngc7746	23.755556	-1.684889
ngc7747	23.758958	27.360944
ngc7748	23.749075	69.754861
ngc7749	23.763208	-29.517806
ngc7750	23.777178	3.799806
ngc7751	23.782872	6.861806
ngc7752	23.782933	29.458917
ngc7753	23.784675	29.483444
ngc7754	23.819781	-16.600583
ngc7755	23.797711	-30.522028
ngc7756	23.807944	4.125167
ngc7757	23.812644	4.171139
ngc7758	23.815328	-22.024194
ngc7759	23.815194	-16.541167
ngc7760	23.819983	30.983139
ngc7762	23.833819	68.037972
ngc7763	23.837694	-16.59
ngc7764	23.848328	-40.728222
ngc7764a	23.889583	-40.810278
ngc7765	23.847822	27.166278
ngc7766	23.848864	27.126306
ngc7767	23.848986	27.087139
ngc7768	23.849606	27.147389
ngc7769	23.851103	20.150417
ngc7770	23.856261	20.096528
ngc7771	23.856892	20.11175
ngc7772	23.862767	16.248139
ngc7773	23.869414	31.276611
ngc7774	23.869778	11.47
ngc7775	23.873458	28.772667
ngc7777	23.886806	28.283444
ngc7778	23.888797	7.870917
ngc7779	23.890775	7.875667
ngc7780	23.892269	8.118139
ngc7781	23.896106	7.860472
ngc7782	23.898303	7.970556
ngc7783	23.903072	0.379944
ngc7784	23.920464	21.762167
ngc7785	23.921953	5.915833
ngc7786	23.92265	21.588056
ngc7787	23.935506	0.549472
ngc7788	23.945994	61.399917
ngc7789	23.956683	56.708278
ngc7790	23.973406	61.208306
ngc7791	23.965917	10.765722
ngc7792	23.967658	16.501417
ngc7793	23.963842	-32.591028
ngc7794	23.976144	10.728139
ngc7795	23.977067	60.034972
ngc7796	23.983269	-55.458306
ngc7797	23.983019	3.634639
ngc7798	23.990417	20.749861
ngc7799	23.992097	31.295611
ngc7800	23.993422	14.805583
ngc7801	0.005956	50.745
ngc7802	0.016783	6.242056
ngc7803	0.022214	13.11125
ngc7804	0.021889	7.749694
ngc7805	0.024103	31.43375
ngc7806	0.025014	31.441861
ngc7807	0.007383	-18.841889
ngc7808	0.058925	-10.744667
ngc7809	0.035958	2.941056
ngc7810	0.038656	12.971639
ngc7811	0.040686	3.351917
ngc7812	0.048464	-34.235639
ngc7814	0.054136	16.145417
ngc7815	0.056897	20.704167
ngc7816	0.063572	7.478639
ngc7817	0.066364	20.752333
ngc7818	0.069125	7.379389
ngc7819	0.073483	31.472056
ngc7820	0.075219	5.200278
ngc7821	0.087978	-16.476917
lbn589,ngc7822	0.059819	67.161639
ngc7823	0.079331	-62.061556
ngc7824	0.085064	6.920111
ngc7825	0.085167	5.203667
ngc7826	0.0887	-20.688278
ngc7827	0.091017	5.222333
ngc7828	0.107519	-13.416111
ngc7829	0.10805	-13.420611
ngc7830	0.100517	8.342778
ngc7833	0.108739	27.639667
ngc7834	0.110506	8.367889
ngc7835	0.112992	8.425944
ngc7836	0.133789	33.070778
ngc7837	0.114275	8.351389
ngc7838	0.114986	8.350861
ngc7839	0.116842	27.635222
ngc7840	0.119111	8.3835
b33,horseheadnebula	5.683056	-2.458333
c9,cavenebula,lbn529,sh2155	22.965	62.518333
c14,doublecluster,hchipersei	2.345	57.1375
c41,hyades,mel025	4.448333	15.866667
c99,coalsacknebula	12.521944	-63.743333
alsufiscluster,brocchiscluster,cl399,coathangerasterism	19.423333	20.183333
largemagellaniccloud,nubeculamajor	5.392917	-69.756111
circinusgalaxy	14.219431	-65.339222
fourcadefigueroa	13.579806	-45.5475
sculptordwarfelliptical	1.002597	-33.709028
fornaxdwarfspheroidal	2.666481	-34.449194
h5	12.454444	-60.778333
h13	17.064167	-48.083333
h20	19.885	18.333333
h21	23.903667	61.74
hcg79,seyfertssextet	15.986639	20.758611
hcg92,stephansquintet	22.599722	33.958333
m40	12.371139	58.084444
m45,mel22,pleiades	3.791278	24.105278
mel71	7.626	-12.055
mel72	7.477444	-10.7
mel101	10.703333	-65.1
mel105	11.328333	-63.483333
comastarcluster,mel111	12.418333	26.1
mwsc3156	19.695669	-33.999472
mwsc3171	19.754	-8.007222
mwsc3561	21.777456	-21.252611
pgc143,wlmgalaxy,wolflundmarkmelotte	0.032822	-15.460917
pgc3853	1.084689	-6.212389
pgc25886	9.180406	-8.890694
pgc29653,sextansa	10.183556	-4.692778
pgc88608,sextansdwarfspheroidal	10.217472	-1.614722
ugc4305	8.31805	70.720028
sextansb,ugc5373	10.000028	5.332222
leoi,ugc5470	10.141139	12.306389"""


def _load_big_catalog(blob):
    catalog = {}
    for line in blob.splitlines():
        if not line:
            continue
        try:
            keys, ra, dec = line.split("\t")
            ra = float(ra)
            dec = float(dec)
        except ValueError:
            continue
        for key in keys.split(","):
            if key:
                catalog[key] = (ra, dec)
    return catalog


BIG_CATALOG = _load_big_catalog(BIG_CATALOG_BLOB)

# Katalogbezeichnung + Nummer aus dem Ordnernamen erkennen, z. B. "NGC 7000",
# "NGC7000", "IC1318", "M 31", "Sh2-140", "LBN 691". Fuehrendes \b sorgt
# dafuer, dass z. B. "Markarjan" nicht faelschlich als "M..." erkannt wird
# (nach "m" muesste sofort eine Ziffer folgen). Am Ende steht bewusst kein \b,
# sondern "keine weitere Ziffer" (?!\d): ein Unterstrich zaehlt fuer \b als
# Wortzeichen, ein reines \b wuerde also z. B. bei zusammengesetzten Namen wie
# "NGC5363_5317_5360" nach der ersten Nummer nicht mehr zutreffen, weil davor
# und danach je ein Wortzeichen (Ziffer/Unterstrich) steht. Caldwell bewusst
# nur ausgeschrieben, da ein blosses "C" + Zahl mit Kometen-Bezeichnungen wie
# "C/2020" kollidieren wuerde.
CATALOG_NUM_PATTERNS = [
    (re.compile(r'\bngc\s*0*(\d{1,4}[a-z]?)(?!\d)', re.IGNORECASE), 'ngc'),
    (re.compile(r'\bic\s*0*(\d{1,4}[a-z]?)(?!\d)', re.IGNORECASE), 'ic'),
    (re.compile(r'\bm\s*0*(\d{1,3})(?!\d)', re.IGNORECASE), 'm'),
    (re.compile(r'\bsh\s*2[\s\-_]*0*(\d{1,3})(?!\d)', re.IGNORECASE), 'sh2'),
    (re.compile(r'\blbn\s*0*(\d{1,4})(?!\d)', re.IGNORECASE), 'lbn'),
    (re.compile(r'\bcaldwell\s*0*(\d{1,3})(?!\d)', re.IGNORECASE), 'c'),
]

MONTH_NAMES = {
    "januar": 1, "jan": 1, "january": 1,
    "februar": 2, "feb": 2, "february": 2,
    "maerz": 3, "märz": 3, "mar": 3, "march": 3,
    "april": 4, "apr": 4,
    "mai": 5, "may": 5,
    "juni": 6, "jun": 6, "june": 6,
    "juli": 7, "jul": 7, "july": 7,
    "august": 8, "aug": 8,
    "september": 9, "sep": 9, "sept": 9,
    "oktober": 10, "okt": 10, "october": 10, "oct": 10,
    "november": 11, "nov": 11,
    "dezember": 12, "dez": 12, "december": 12, "dec": 12,
}

MONTHS_DE_SHORT = ["Jan","Feb","Mär","Apr","Mai","Jun","Jul","Aug","Sep","Okt","Nov","Dez"]

FINAL_EXT = {".jpg", ".jpeg", ".png", ".tif", ".tiff", ".psd", ".psb", ".mp4"}
RAW_EXT = {".fit", ".fits", ".fts", ".cr2", ".cr3", ".nef", ".arw", ".dng", ".raf"}
# CALIB_WORDS ist eine Einstellung (siehe apply_config()); der Wert hier ist
# nur die Vorgabe, falls apply_config() aus irgendeinem Grund uebersprungen
# wuerde. STACK_WORDS ist bewusst kein Einstellungsfeld (rein technisches
# Erkennungsmerkmal fuer bereits gestackte Zwischendateien).
CALIB_WORDS = tuple(DEFAULT_CONFIG["calib_words"])
STACK_WORDS = ("stack", "masterlight", "integration", "pixinsight", "_pi")

HOUR_IN_NAME_RE = re.compile(r'(\d+(?:[.,]\d+)?)\s*h(?:ours?)?(?:[_\s]|$)', re.IGNORECASE)
DATE_IN_NAME_RE = re.compile(r'(\d{1,2})[.\-_](\d{1,2})[.\-_](\d{2,4})')

# Light_<Ziel>_<Belichtung>s_Bin<n>_<Kamera[_Filter]>_gain<g>_<Zeitstempel>_<Nr>.fit
# Nach dem Zeitstempel haengt ASIAIR/NINA je nach Version und Einstellung
# noch zusaetzliche Felder an (z. B. Meridian-/Rotatorwinkel wie "91deg",
# Sensortemperatur wie "-0.1C", teils beides zusammen, teils gar keines).
# Statt ein einzelnes optionales Temperaturfeld fest vorzusehen (das aeltere
# Format), wird hier eine beliebige Anzahl solcher "_irgendwas"-Felder
# uebersprungen, bis die abschliessende "_<Nummer>.<Endung>" gefunden wird -
# das deckt alte wie neue Namensschemata gleichermassen ab.
LIGHT_NAME_RE = re.compile(
    r'^(?P<type>Light)_[^_]*_(?P<exp>[\d.]+)s_Bin\d+_(?P<mid>.+?)_gain\d+_'
    r'(?P<ts>\d{8}-\d{6})(?:_[^_]+)*_(?P<seq>\d+)\.\w+$',
    re.IGNORECASE)

# Zweite Variante: ASIAIR mit DSLR/Systemkamera (z. B. Sony A7R III) statt
# ZWO-ASI-Astrokamera. Dort sieht derselbe Aufnahmetyp so aus:
#   Light_C 27 AM  400mm_210.0s_Bin1_ISO1600_20260710-033413_270deg_25.0C_A7RIIIJ_0001.fit
# Zwei Unterschiede zum Muster oben: statt "gain<Zahl>" steht dort
# "ISO<Zahl>", und VOR diesem Feld steht keine Kamerabezeichnung - die
# taucht stattdessen hinten zwischen den Zusatzfeldern auf (hier
# "A7RIIIJ", siehe camera_from_extra_fields()).
#
# WICHTIG, bewusst als EIGENES Muster statt als Erweiterung von
# LIGHT_NAME_RE: scan_project() probiert immer zuerst das Muster oben und
# nur bei Nichttreffer dieses hier. Ein Dateiname, der bisher erkannt
# wurde, nimmt dadurch buchstaeblich denselben Weg wie vorher - das
# bisherige Schema kann durch diese Erweiterung also nicht beeinflusst
# werden, unabhaengig davon, wie dieses Muster hier formuliert ist.
#
# "gain" ist hier absichtlich auch erlaubt: Damit werden zusaetzlich
# ASI-Namen OHNE Kamerafeld erkannt (".._Bin1_gain100_.."), die am Muster
# oben bisher ebenfalls gescheitert sind.
LIGHT_NAME_DSLR_RE = re.compile(
    r'^(?P<type>Light)_[^_]*_(?P<exp>[\d.]+)s_Bin\d+_(?:iso|gain)\d+_'
    r'(?P<ts>\d{8}-\d{6})(?P<extra>(?:_[^_]+)*)_(?P<seq>\d+)\.\w+$',
    re.IGNORECASE)

# Zusatzfelder, die ASIAIR/NINA hinter den Zeitstempel haengen und die
# sicher KEINE Kamerabezeichnung sind: Rotator-/Meridianwinkel ("270deg"),
# Sensortemperatur ("25.0C", "-0.1C"), Brennweite ("400mm"), Blende
# ("f2.8"), Binning, ISO/Gain, Belichtung, Prozentangaben und reine Zahlen.
_EXTRA_TECH_FIELD_RE = re.compile(
    r'^(?:-?[\d.]+c|[\d.]+deg|[\d.]+mm|f[\d.]+|bin\d+|(?:iso|gain)\d+'
    r'|[\d.]+s|[\d.]+%|[\d.]+)$',
    re.IGNORECASE)


def camera_from_extra_fields(extra):
    """extra: der Teil des Dateinamens hinter dem Zeitstempel und vor der
    laufenden Nummer, mit fuehrendem Unterstrich (z. B.
    "_270deg_25.0C_A7RIIIJ"). Beim ASIAIR mit DSLR/Systemkamera steht die
    Kamerabezeichnung dort statt vor dem ISO-Feld. Technische Felder
    (Winkel, Temperatur, Brennweite, ...) werden uebersprungen, das
    hinterste verbleibende Feld gilt als Kamerabezeichnung.

    Kommt nichts in Frage, wird "" zurueckgegeben - die Aufnahme zaehlt
    dann wie bisher unter "unbekannt" (dieselbe Behandlung wie bei einem
    Dateinamen, der nur einen Filter und keine Kamera enthaelt)."""
    tokens = [t for t in (extra or "").split("_") if t]
    for token in reversed(tokens):
        if not _EXTRA_TECH_FIELD_RE.match(token):
            return token
    return ""

# FILTER_MAP und CAMERA_MAP sind Einstellungen (siehe apply_config()); die
# Werte hier sind nur die Vorgabe, falls apply_config() aus irgendeinem
# Grund uebersprungen wuerde. Kamera-Modellnummer (aus dem Dateinamen, z. B.
# "2600") auf einen sprechenden Basisnamen abbilden: Ob Mono (MM) oder
# Farbe/OSC (MC) vorliegt, wird separat ermittelt (aus einem MM/MC-Hinweis
# im Namen, sonst aus der Filternutzung) und automatisch angehaengt, muss
# in CAMERA_MAP also nicht eingetragen werden.
FILTER_MAP = dict(DEFAULT_CONFIG["filter_map"])
CAMERA_MAP = dict(DEFAULT_CONFIG["camera_map"])

CAMERA_MODEL_RE = re.compile(r'(\d{3,4})')


def extract_camera_model(camera_raw):
    m = CAMERA_MODEL_RE.search(camera_raw)
    return m.group(1) if m else camera_raw


def explicit_camera_variant(camera_raw):
    low = camera_raw.lower()
    if re.search(r'(?<![a-z])mm(?![a-z])', low):
        return "MM"
    if re.search(r'(?<![a-z])mc(?![a-z])', low):
        return "MC"
    return None

CATEGORY_KEYWORDS = [
    ("Komet", ["komet", "c/20", "c/19", "p/pons", "ztf", "neowise"]),
    ("Mond", ["mond", "moon"]),
    ("Planet", ["mars", "saturn", "jupiter", "venus", "merkur", "neptun", "uranus"]),
    ("Konjunktion", ["konjunktion"]),
    ("Sternhaufen", ["sternhaufen", "cluster", "persei", "praesepe", "beehive"]),
    ("Galaxienhaufen", ["galaxienhaufen", "markarjan", "markarian", "coma", "abell 16", "lgg"]),
    # "ngc 69" bewusst NICHT als Bereich (69xx): NGC 6960/6974/6979/6992/6995
    # liegen ebenfalls in diesem Bereich, gehoeren aber zum
    # Cirrusnebel/Schleiernebel (Emissionsnebel, kein Galaxie) - ein
    # Nutzer hat genau diese Fehlklassifizierung bei NGC 6960 gemeldet.
    # Stattdessen die konkrete, tatsaechlich gemeinte Galaxie benennen.
    ("Galaxie", ["galaxie", "galaxy", "ngc 4", "ngc 5", "ngc 6946", "m31", "m81", "m63", "m101"]),
]


# ======================================================================
# Sonnenposition / Sichtbarkeit (Naeherung, siehe Methodik im Dashboard)
# ======================================================================

def sun_ra_hours(days_since_j2000):
    L = math.radians((280.460 + 0.9856474 * days_since_j2000) % 360)
    g = math.radians((357.528 + 0.9856003 * days_since_j2000) % 360)
    lam = L + math.radians(1.915) * math.sin(g) + math.radians(0.020) * math.sin(2 * g)
    eps = math.radians(23.439 - 0.0000004 * days_since_j2000)
    ra = math.atan2(math.cos(eps) * math.sin(lam), math.cos(lam))
    return (math.degrees(ra) / 15) % 24


J2000 = date(2000, 1, 1)


def opposition_date(ra_obj_h, year):
    target = (ra_obj_h - 12) % 24
    best_date, best_diff = None, 999
    d0 = date(year, 1, 1)
    for i in range(370):
        d = d0 + timedelta(days=i)
        n = (d - J2000).days
        diff = min(abs(sun_ra_hours(n) - target), 24 - abs(sun_ra_hours(n) - target))
        if diff < best_diff:
            best_diff, best_date = diff, d
    return best_date


def compute_obs(ra_h, dec_deg, ref_year):
    od = opposition_date(ra_h, ref_year)
    alt = round(90 - abs(LATITUDE - dec_deg))
    cp = dec_deg > (90 - LATITUDE)
    win_start = ((od - timedelta(days=90)).month)
    win_end = ((od + timedelta(days=90)).month)
    peak_day = od.day
    peak_label = ("Anfang " if peak_day <= 10 else "Mitte " if peak_day <= 20 else "Ende ") + MONTHS_DE_SHORT[od.month - 1]
    return {"winStart": win_start, "winEnd": win_end, "peak": peak_label, "alt": alt, "cp": cp}


# ======================================================================
# Ordner-Scan
# ======================================================================

def classify_category(name):
    lname = name.lower()
    for cat, keywords in CATEGORY_KEYWORDS:
        if any(k in lname for k in keywords):
            return cat
    return "Nebel/Deep-Sky"


def has_month_hint(name):
    lname = re.sub(r'[^a-zäöüß]', ' ', name.lower())
    for word in lname.split():
        if word in MONTH_NAMES:
            return word.capitalize()
    return None


def parse_hours_from_dirname(name):
    m = HOUR_IN_NAME_RE.search(name)
    if not m:
        return None
    return float(m.group(1).replace(",", "."))


def looks_like_session_dir(name):
    lname = name.lower()
    return bool(DATE_IN_NAME_RE.search(name)) or "nacht" in lname or "session" in lname


def _scandir_walk(top):
    """Wie os.walk(path), liefert bei den Dateien aber DirEntry-Objekte
    statt blosser Namen (dirnames bleibt eine gewoehnliche Namensliste,
    In-Place-Pruning zum Ueberspringen von Unterordnern funktioniert also
    weiterhin wie bei os.walk).

    Grund: DirEntry.stat() beantwortet unter Windows Groesse/Zeitstempel
    aus den Metadaten, die FindFirstFile/FindNextFile beim Auflisten des
    Ordners ohnehin schon mitliefert - ohne weiteren Dateisystemzugriff.
    Das bisherige os.walk() + separates os.path.getsize() pro Datei loeste
    dagegen einen zusaetzlichen Aufruf JE DATEI aus (der einzeln eine
    Datei-Handle oeffnet), was bei Ordnern mit vielen tausend Dateien ein
    Echtzeit-Virenschutz einzeln abfangen und sichtbar verzoegern kann. Ein
    per faulthandler aufgezeichneter Haenger blieb genau in diesem
    os.path.getsize()-Aufruf haengen (Ordner mit 2445 Dateien) - dieser
    Umbau vermeidet den zusaetzlichen Aufruf von vornherein."""
    try:
        entries = list(os.scandir(top))
    except OSError:
        return
    dirnames = []
    subdir_paths = {}
    direntries = []
    for e in entries:
        try:
            is_dir = e.is_dir(follow_symlinks=False)
        except OSError:
            is_dir = False
        if is_dir:
            dirnames.append(e.name)
            subdir_paths[e.name] = e.path
        else:
            direntries.append(e)
    yield top, dirnames, direntries
    for name in dirnames:  # dirnames erst NACH dem yield lesen (Pruning beachten)
        yield from _scandir_walk(subdir_paths[name])


def _dir_size_only(path):
    """Summiert nur die Dateigroessen unter path, ohne jede Datei zu oeffnen
    oder gegen ein Namensschema zu pruefen. Wird fuer uebersprungene
    Kalibrierordner verwendet, damit deren Speicherplatz in der Datenmenge
    auftaucht, ohne den Performance-Vorteil des kompletten Ueberspringens
    fuer die eigentliche Auswertung (Filter/Kamera/Vorschau) zu verlieren."""
    total = 0
    for _dirpath, _dirnames, direntries in _scandir_walk(path):
        for e in direntries:
            try:
                total += e.stat(follow_symlinks=False).st_size
            except OSError:
                pass
    return total


def scan_project(path):
    """Läuft rekursiv durch einen Projektordner und sammelt Kennzahlen."""
    result = {
        "filters": {},          # Label -> {"count": n, "seconds": s}
        "cameras": {},          # Label -> {"count": n, "seconds": s, "filtered": n, "unfiltered": n}
        "final_files": [],
        "stack_dirs_seen": False,
        "raw_count": 0,
        "hours_from_names": 0.0,
        "hours_from_names_found": False,
        "session_hours": {},    # relative Unterordner -> Stunden (aus Namen)
        "dates_seen": set(),
        "total_files": 0,
        "total_bytes": 0,       # Datenmenge auf der Platte, inkl. Kalibrierordner
        "last_modified": 0.0,   # juengste Aenderungszeit (Unix-Timestamp) unter den verarbeiteten Dateien
    }

    for dirpath, dirnames, direntries in _scandir_walk(path):
        rel = os.path.relpath(dirpath, path)
        base = os.path.basename(dirpath).lower()
        if any(w in base for w in STACK_WORDS):
            result["stack_dirs_seen"] = True

        # Kalibrierordner (Flats/Darks/Bias/...) enthalten nie Lights, koennen
        # aber zehntausende Dateien umfassen. In-place aus dirnames entfernen,
        # damit os.walk gar nicht erst mit der vollen Pro-Datei-Logik (Regex,
        # Endungspruefung, Vorschau-Kandidaten, ...) hineinsteigt - das ist
        # der groesste Hebel fuer die Scan-Geschwindigkeit bei umfangreichen
        # Archiven. Fuer die Datenmenge zaehlt dieser Inhalt aber sehr wohl
        # (ein Projekt mit vielen Flats/Darks belegt echten Speicherplatz),
        # deshalb wird davor noch schnell nur die Groesse aufsummiert, ohne
        # jede Datei einzeln zu klassifizieren.
        pruned = [d for d in dirnames if any(w in d.lower() for w in CALIB_WORDS)]
        if pruned:
            dirnames[:] = [d for d in dirnames if d not in pruned]
            for d in pruned:
                result["total_bytes"] += _dir_size_only(os.path.join(dirpath, d))

        # Stunden direkt im (Unter-)Ordnernamen?
        h = parse_hours_from_dirname(os.path.basename(dirpath))
        if h is not None and rel != ".":
            result["session_hours"][rel] = h

        for entry in direntries:
            fn = entry.name
            result["total_files"] += 1
            full_fn = entry.path
            try:
                # DirEntry.stat() nutzt die beim Auflisten des Ordners
                # bereits vorliegenden Metadaten, kein separater
                # Dateisystemzugriff pro Datei (siehe _scandir_walk).
                st = entry.stat(follow_symlinks=False)
                size, mtime = st.st_size, st.st_mtime
            except OSError:
                size, mtime = 0, 0.0
            result["total_bytes"] += size
            if mtime > result["last_modified"]:
                result["last_modified"] = mtime
            ext = os.path.splitext(fn)[1].lower()
            lfn = fn.lower()

            if ext in FINAL_EXT:
                # Groesse+mtime gleich mitspeichern (siehe pick_preview_file
                # und get_thumbnail_cached): so muss die gewaehlte Datei
                # spaeter fuer Vorschauauswahl/Cache-Pruefung kein zweites
                # Mal einzeln angefasst werden.
                result["final_files"].append((os.path.join(rel, fn), size, mtime))
                continue

            if any(w in lfn for w in CALIB_WORDS) or any(w in base for w in CALIB_WORDS):
                continue  # Kalibrierdaten zaehlen nicht als Light

            if ext in RAW_EXT:
                # Zuerst immer das bisherige ASI-Muster; nur wenn das nicht
                # passt, die DSLR-/ISO-Variante (siehe Kommentar bei
                # LIGHT_NAME_DSLR_RE). Bei Variante 1 steckt die Kamera im
                # mid-Feld vor "gain", bei Variante 2 in den Zusatzfeldern
                # hinter dem Zeitstempel.
                m = LIGHT_NAME_RE.match(fn)
                if m:
                    mid = m.group("mid")
                else:
                    m = LIGHT_NAME_DSLR_RE.match(fn)
                    mid = camera_from_extra_fields(m.group("extra")) if m else ""
                if m:
                    exp = float(m.group("exp"))
                    parts = [p for p in mid.split("_") if p]
                    filt = None
                    cam_parts = parts
                    # als Filter werten, wenn der letzte Teil ein bekannter
                    # Filtercode ist – unabhaengig davon, ob noch ein
                    # Kamera-Teil davor steht. Frueher war hier zusaetzlich
                    # mindestens 2 Teile verlangt, wodurch ein Dateiname ohne
                    # Kamera-Feld (z. B. "..._Bin1_H_gain100_...") den Filter
                    # "H" faelschlich als Kamera "H" gezaehlt hat.
                    if parts and parts[-1].upper() in FILTER_MAP:
                        filt = parts[-1].upper()
                        cam_parts = parts[:-1]
                    label = FILTER_MAP.get(filt, "OSC/kein Filter")
                    entry = result["filters"].setdefault(label, {"count": 0, "seconds": 0.0})
                    entry["count"] += 1
                    entry["seconds"] += exp
                    result["hours_from_names_found"] = True
                    ts = m.group("ts")[:8]
                    result["dates_seen"].add(ts)

                    camera_raw = "_".join(cam_parts) if cam_parts else "unbekannt"
                    # hier bewusst noch der Rohcode als Schluessel (z. B. "2600",
                    # "2600MC_RGB"); die Zusammenfuehrung nach Modellnummer und
                    # Farbe/Mono passiert zentral in scan_root() ueber alle
                    # Projekte hinweg, damit die Herleitung auf mehr Daten beruht
                    cam_entry = result["cameras"].setdefault(
                        camera_raw, {"count": 0, "seconds": 0.0, "filtered": 0, "unfiltered": 0})
                    cam_entry["count"] += 1
                    cam_entry["seconds"] += exp
                    if filt:
                        cam_entry["filtered"] += 1
                    else:
                        cam_entry["unfiltered"] += 1
                else:
                    result["raw_count"] += 1
                    dm = DATE_IN_NAME_RE.search(fn)
                    if dm:
                        result["dates_seen"].add(dm.group(0))

    return result


_DISPLAY_NAME_DONE_RE = re.compile(
    r'\s*[-–_]?\s*(?<![a-z0-9])(?:done|fertig)(?![a-z0-9])\.?\s*$', re.IGNORECASE)


def clean_display_name(name):
    """Entfernt eine abschliessende "- Done"/"- Fertig"-Markierung aus dem
    ANGEZEIGTEN Objektnamen (Nutzerwunsch: der Status wird bereits ueber
    die Fertig-Pille angezeigt, im Namen selbst ist das Tag redundant).
    Wirkt nur auf das Namensfeld fuer die Anzeige - der uebergebene rohe
    Ordnername bleibt fuer detect_status() (weiter unten), die Merge-
    Verarbeitung und zum Oeffnen des Ordners unveraendert massgeblich."""
    cleaned = _DISPLAY_NAME_DONE_RE.sub('', name).rstrip(' -_')
    return cleaned if cleaned else name


def detect_status(name, scan):
    lname = name.lower()
    # 1. Done-/Fertig-Tag (beide gleichwertig, je nach Vorliebe des Nutzers;
    # mit Bindestrich, Leerzeichen ODER Unterstrich davor/danach). Bewusst
    # kein \b vor/nach dem Tag: "_" zaehlt fuer \b als Wortzeichen, "M31_Done"
    # haette also KEINE Wortgrenze zwischen "_" und "D" und wuerde mit \b
    # faelschlich nicht erkannt. Die Lookaround-Pruefung auf Buchstaben/
    # Ziffern (statt ganzer Wortzeichen) behandelt "_" korrekt als Trenner.
    if re.search(r'(?<![a-z0-9])(?:done|fertig)(?![a-z0-9])', lname):
        return "done", None
    # 2. fertige Datei vorhanden, aber (noch) kein "done" im Namen -> In
    # Arbeit statt automatisch als Fertig zu gelten. Nur das explizite
    # "done"-Tag (Regel 1) markiert ein Projekt als tatsaechlich fertig.
    if scan["final_files"]:
        return "wip", None
    # 3. Monatshinweis im Namen
    month = has_month_hint(name)
    if month:
        return "open-date", month
    # 4. nur Rohdaten, kein Stack
    has_lights = bool(scan["filters"]) or scan["raw_count"] > 0
    if has_lights and not scan["stack_dirs_seen"]:
        return "raw-only", None
    # 5. Stack vorhanden, kein Endbild
    if scan["stack_dirs_seen"] or has_lights:
        return "unclear", None
    # 6. kaum etwas vorhanden
    return "barely", None


def total_hours(scan):
    if scan["session_hours"]:
        return round(sum(scan["session_hours"].values()), 2), True
    if scan["hours_from_names_found"]:
        secs = sum(v["seconds"] for v in scan["filters"].values())
        return round(secs / 3600, 2), True
    return None, False


def format_cameras(scan):
    parts = []
    for label, v in sorted(scan["cameras"].items(), key=lambda kv: -kv[1]["count"]):
        tag = "mit Filter" if v["filtered"] and not v["unfiltered"] else \
              "OSC" if v["unfiltered"] and not v["filtered"] else \
              "gemischt"
        parts.append(f"{label} {v['count']}× ({tag})")
    return " · ".join(parts) if parts else "–"


def format_filters(scan):
    """Nur die Zusammenfassung je Filter (z. B. "Luminance 319x300s"), nie
    die einzelnen Nacht-/Session-Unterordnernamen aus scan["session_hours"]
    (Nutzerwunsch: machte die Zeile bei Projekten mit vielen Naechten sehr
    hoch und war gegenueber der Std.-gesamt-Spalte redundant)."""
    parts = []
    for label, v in sorted(scan["filters"].items()):
        parts.append(f"{label} {v['count']}×{v['seconds']/v['count']:.0f}s")
    if not parts and scan["raw_count"]:
        parts.append(f"{scan['raw_count']} Rohaufnahmen ohne auswertbares Namensschema")
    return " · ".join(parts) if parts else "–"


def load_object_cache(cache_path):
    try:
        with open(cache_path, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return {}


def save_object_cache(cache_path, cache):
    try:
        with open(cache_path, "w", encoding="utf-8") as f:
            json.dump(cache, f)
    except Exception:
        pass  # auch dieser Zwischenspeicher ist nur eine Optimierung, kein Muss


# Sesame (CDS Strasbourg, seit Jahrzehnten stabiler oeffentlicher Dienst) loest
# gaengige astronomische Namen/Katalognummern in Koordinaten auf und fragt
# dafuer selbst wieder SIMBAD/NED/VizieR ab. "SNV" = alle drei Datenbanken.
# Zweite URL (Harvard-Spiegel) als Fallback, falls die erste nicht erreichbar
# ist. %J-Zeile der Antwort: Rektaszension und Deklination in Dezimalgrad.
SESAME_URLS = [
    "https://cds.unistra.fr/cgi-bin/nph-sesame/SNV?",
    "http://vizier.cfa.harvard.edu/viz-bin/nph-sesame/SNV?",
]
SESAME_RESULT_RE = re.compile(r'%J\s*([0-9.]+)\s*([+\-.0-9]+)')


def _fetch_url_with_hard_timeout(url, timeout):
    """Wie urlopen(url, timeout=timeout), aber mit einer zusaetzlichen,
    vom Socket unabhaengigen Notbremse in einem separaten Thread.

    Beobachtet auf Windows/Python 3.14: Der cds.unistra.fr-Server stoesst
    waehrend des TLS-Handshakes eine Renegotiation an; in diesem Fall hat
    der timeout-Parameter von urlopen() den Aufruf nicht wie erwartet nach
    ein paar Sekunden abgebrochen, sondern der Aufruf blieb unbegrenzt
    haengen und damit der komplette Scan. Der Daemon-Thread hier stellt
    sicher, dass resolve_object_online() spaetestens nach timeout+1s
    weitermacht, selbst wenn der Netzwerk-Request selbst nie zurueckkehrt."""
    result = {}

    def worker():
        try:
            with urlopen(url, timeout=timeout) as resp:
                result["text"] = resp.read().decode("utf-8", errors="replace")
        except Exception as exc:
            result["error"] = exc

    thread = threading.Thread(target=worker, daemon=True)
    thread.start()
    thread.join(timeout + 1)
    if thread.is_alive():
        url_for_msg = getattr(url, "full_url", url)
        raise TimeoutError(f"Kein Ergebnis von {url_for_msg} nach {timeout + 1}s")
    if "error" in result:
        raise result["error"]
    return result.get("text", "")


LEADING_DATE_RE = re.compile(r'^\s*\d{1,2}[.\-]\d{1,2}[.\-]\d{2,4}\s+')
LEADING_COMPACT_DATE_RE = re.compile(r'^\s*\d{6,8}\s+')


def clean_query_name(name):
    """Leitet aus dem Ordnernamen einen sinnvollen Suchbegriff fuer die
    Online-Namensaufloesung ab. Dane haengt an seine Ordnernamen ueblicherweise
    per " - " getrennt einen deutschen Beinamen und/oder den Status an (z. B.
    "IC 1318 - Schmetterlingsnebel - Cygni-Nebel - Done"); davon ist nur der
    erste Teil eine Katalogbezeichnung, die Sesame kennen kann.

    Bei kurzen Einzelnacht-Ordnern nutzt Dane statt " - " oft ein
    vorangestelltes Datum, getrennt per Unterstrich (z. B. "28.06.20_Sadr"
    oder "190719_partielle_Mondfinsternis"). Ohne das Entfernen dieses
    Datums wuerde die Anfrage bei Sesame immer scheitern, weil das Datum
    keine gueltige Katalogbezeichnung ist."""
    part = name.split(" - ")[0]
    part = part.replace("_", " ").strip()
    part = LEADING_DATE_RE.sub("", part)
    part = LEADING_COMPACT_DATE_RE.sub("", part)
    return part.strip()


def resolve_object_online(name, old_cache, used_cache, stats):
    """Fragt bei alten Cache-Treffern nichts erneut ab, sonst einmalig Sesame.

    stats ist ein ueber den ganzen Lauf geteiltes Dict. Sobald ein Netzwerk-
    fehler auftritt (nicht: "Objekt unbekannt", sondern echte Nichterreich-
    barkeit), wird stats["network_dead"] gesetzt, damit nicht fuer jedes
    weitere unbekannte Objekt im selben Lauf erneut der volle Timeout anfaellt."""
    query = clean_query_name(name)
    key = query.lower()
    if not key:
        return None
    if key in old_cache:
        used_cache[key] = old_cache[key]
        stats["hits"] += 1
        coords = old_cache[key]
        return tuple(coords) if coords else None

    if stats.get("network_dead"):
        return None

    encoded = quote(query, safe="")
    for base_url in SESAME_URLS:
        try:
            text = _fetch_url_with_hard_timeout(base_url + encoded, ONLINE_LOOKUP_TIMEOUT)
            m = SESAME_RESULT_RE.search(text)
            if m:
                ra_deg, dec_deg = float(m.group(1)), float(m.group(2))
                coords = (ra_deg / 15.0, dec_deg)
                used_cache[key] = list(coords)
                stats["new"] += 1
                return coords
            # Antwort kam an, aber kein Treffer -> Objekt bleibt dauerhaft
            # unbekannt, das wird gespeichert, damit nicht bei jedem Start
            # erneut online nachgefragt wird.
            used_cache[key] = None
            stats["notfound"] += 1
            return None
        except (URLError, HTTPError, TimeoutError, OSError):
            continue  # naechste URL (Spiegel-Server) probieren
    # keine der URLs erreichbar -> Netzwerkproblem, nicht das Objekt selbst
    stats["network_dead"] = True
    stats["failed"] += 1
    return None


# Ortsnamen-Aufloesung fuer die Einstellungen (Standort-Feld): Nominatim ist
# der oeffentliche Geokodierungsdienst von OpenStreetMap. Nutzungsbedingungen
# verlangen einen aussagekraeftigen User-Agent und keine automatisierten/
# wiederholten Anfragen - hier bewusst nur einmalig per Knopfdruck im
# Einstellungen-Panel ausgeloest, nie automatisch im Hintergrund.
NOMINATIM_URL = "https://nominatim.openstreetmap.org/search?"
NOMINATIM_USER_AGENT = "AstroLogbuch/1 (persoenliches Astrofoto-Dashboard, kein Webdienst)"
NOMINATIM_TIMEOUT = 5


def resolve_place_latitude(place_name):
    """Fragt den Breitengrad eines Ortsnamens bei Nominatim/OpenStreetMap ab,
    fuer Nutzer, die keine Koordinate im Kopf haben. Nur die Zahl wird
    verwendet (Laengengrad spielt fuer die Sichtbarkeitsberechnung in diesem
    Programm keine Rolle, siehe compute_obs()). Gibt ein Dict mit "ok" und
    entweder "latitude"+"displayName" oder "error" zurueck."""
    query = (place_name or "").strip()
    if not query:
        return {"ok": False, "error": "Bitte einen Ort eingeben."}
    url = NOMINATIM_URL + urlencode({"q": query, "format": "json", "limit": 1})
    req = Request(url, headers={"User-Agent": NOMINATIM_USER_AGENT})
    try:
        text = _fetch_url_with_hard_timeout(req, NOMINATIM_TIMEOUT)
    except TimeoutError:
        return {"ok": False, "error": "Zeitüberschreitung beim Nachschlagen (kein Internet?)."}
    except (URLError, HTTPError, OSError) as exc:
        return {"ok": False, "error": f"Nachschlagen fehlgeschlagen: {exc}"}
    try:
        results = json.loads(text)
    except (ValueError, TypeError):
        return {"ok": False, "error": "Unerwartete Antwort beim Nachschlagen."}
    if not results:
        return {"ok": False, "error": f'Ort "{place_name}" nicht gefunden.'}
    top = results[0]
    try:
        latitude = round(float(top["lat"]), 4)
    except (KeyError, ValueError, TypeError):
        return {"ok": False, "error": "Unerwartete Antwort beim Nachschlagen."}
    return {"ok": True, "latitude": latitude, "displayName": top.get("display_name", query)}


def find_object_coords(name, category=None, online_cache_old=None, online_cache_used=None, online_stats=None):
    # 1. Handgepflegter Katalog fuer Spezialfaelle und deutsche Namen
    lname = name.lower()
    for key, coords in OBJECT_CATALOG.items():
        if key in lname:
            return coords

    # Kometen haben keine feste Position (sie bewegen sich staendig relativ zu
    # den Sternen), ein "optimales Fenster" waere hier fachlich falsch bzw.
    # irrefuehrend. Das ist eine strukturelle Einschraenkung, kein Fehler.
    if category == "Komet":
        return None

    # 2. Grosser eingebauter Katalog (NGC/IC/Messier/Sh2/LBN/Caldwell), rein
    # ueber die Katalognummer im Ordnernamen erkannt
    for pattern, prefix in CATALOG_NUM_PATTERNS:
        m = pattern.search(name)
        if m:
            key = prefix + m.group(1).lower()
            if key in BIG_CATALOG:
                return BIG_CATALOG[key]

    # 3. Online-Namensaufloesung (nur wenn aktiviert und ein Cache uebergeben
    # wurde, also nur waehrend eines echten Scans, nicht in Tests etc.)
    if ONLINE_LOOKUP_ENABLED and online_cache_used is not None:
        return resolve_object_online(
            name, online_cache_old or {}, online_cache_used,
            online_stats if online_stats is not None else {
                "hits": 0, "new": 0, "notfound": 0, "failed": 0, "network_dead": False})

    return None


def merge_scans(dst, src):
    """Zaehlt die Kennzahlen von src in dst hinein (fuer MERGE_INTO)."""
    for label, v in src["filters"].items():
        e = dst["filters"].setdefault(label, {"count": 0, "seconds": 0.0})
        e["count"] += v["count"]; e["seconds"] += v["seconds"]
    for label, v in src["cameras"].items():
        e = dst["cameras"].setdefault(label, {"count": 0, "seconds": 0.0, "filtered": 0, "unfiltered": 0})
        e["count"] += v["count"]; e["seconds"] += v["seconds"]
        e["filtered"] += v["filtered"]; e["unfiltered"] += v["unfiltered"]
    dst["final_files"].extend(src["final_files"])
    dst["stack_dirs_seen"] = dst["stack_dirs_seen"] or src["stack_dirs_seen"]
    dst["raw_count"] += src["raw_count"]
    dst["session_hours"].update(src["session_hours"])
    dst["dates_seen"] |= src["dates_seen"]
    dst["total_files"] += src["total_files"]
    dst["total_bytes"] += src["total_bytes"]
    dst["last_modified"] = max(dst["last_modified"], src["last_modified"])


PREVIEW_EXT_SET = {".jpg", ".jpeg", ".png", ".tif", ".tiff"}

# jpg/png sind in der Astro-Bearbeitung so gut wie immer der fertig
# gestreckte/farbkorrigierte Export zum Anschauen; ein separates TIF/TIFF
# kann dagegen auch ein unbearbeiteter linearer Master sein, der roh
# angezeigt schwarz oder komplett weiss wirkt. Deshalb bei der Auswahl
# bevorzugt.
PREVIEW_EXT_TIER = {".jpg": 0, ".jpeg": 0, ".png": 0, ".tif": 1, ".tiff": 1}

# Namensfragmente, die eher auf einen Screenshot/Beleg oder ein
# Diagnose-/Annotationsbild als auf das eigentliche fertige Astrofoto
# hindeuten (z. B. ein Screenshot der Aufnahmesoftware, oder ein von
# PixInsight/Astrometry erzeugtes "annotated"-Bild mit Koordinatengitter
# und Beschriftungen, das zufaellig auch als .jpg/.png im Ordner liegt)
SCREENSHOT_HINTS = ("screenshot", "bildschirmfoto", "screen_", "settings",
                    "einstellung", "log_", "info_", "annotated", "annotiert",
                    "solved", "platesolve", "astrometry", "grid")


def pick_preview_file(project_path, final_files):
    """Waehlt unter den fertigen Bilddateien die wahrscheinlichste echte
    Aufnahme aus: keine Screenshot-/Annotations-artigen Dateinamen, jpg/png
    vor tif/tiff (siehe PREVIEW_EXT_TIER), und innerhalb dessen die groesste
    Datei. Bewusst ueber die Dateigroesse auf der Festplatte statt ueber ein
    tatsaechliches Oeffnen jeder Kandidatendatei entschieden: Bilddateien
    muessen dafuer sonst pro Projekt alle einzeln dekodiert werden, was bei
    grossen TIFFs spuerbar Zeit kostet (und die einzige tatsaechlich noetige
    Dekodierung passiert ohnehin in make_thumbnail() fuer die eine gewaehlte
    Datei).

    final_files ist eine Liste aus (rel_pfad, groesse, mtime)-Tripeln, beide
    Metadaten stammen direkt aus scan_project()/_scandir_walk() (dasselbe
    Metadatum, das das Auflisten des Ordners ohnehin schon liefert) - hier
    also bewusst KEIN erneuter Dateisystemzugriff pro Kandidat mehr, das war
    vorher eine beobachtete Haenger-Quelle (siehe _scandir_walk-Kommentar).
    Gibt (voller_pfad, groesse, mtime) zurueck, oder None, damit auch
    get_thumbnail_cached() die gewaehlte Datei nicht noch einmal einzeln
    anfassen muss."""
    candidates = []
    for rel, size, mtime in final_files:
        ext = os.path.splitext(rel)[1].lower()
        if ext not in PREVIEW_EXT_SET:
            continue
        full = os.path.join(project_path, rel)
        lname = os.path.basename(rel).lower()
        suspect = any(h in lname for h in SCREENSHOT_HINTS)
        tier = PREVIEW_EXT_TIER.get(ext, 2)
        candidates.append((suspect, tier, -size, full, size, mtime))
    if not candidates:
        return None
    candidates.sort(key=lambda c: c[:3])
    _, _, _, full, size, mtime = candidates[0]
    return full, size, mtime


# Bildmodi, die Pillow beim direkten .convert("RGB") NICHT auf 0-255
# skaliert, sondern einfach abschneidet: 16-Bit-Graustufen (z. B. aus einem
# unbearbeiteten/linearen Master-TIFF eines Mono-Kamerastacks) landen dann
# fast vollstaendig oberhalb von 255 und werden zu einem komplett weissen
# Bild. Fuer diese Modi wird deshalb zuerst anhand der tatsaechlich
# vorkommenden Werte linear auf 0-255 gestreckt.
HIGH_BITDEPTH_MODES = {"I", "I;16", "I;16B", "I;16L", "I;16N", "F"}


def _rescale_high_bitdepth(im):
    if im.mode not in HIGH_BITDEPTH_MODES:
        return im
    try:
        lo, hi = im.getextrema()
    except Exception:
        return im
    if hi <= lo:
        return im
    scale = 255.0 / (hi - lo)
    # Pillow erkennt diesen Ausdruck als lineare Transformation und rechnet
    # sie in einem Schritt ueber das ganze Bild, nicht Pixel fuer Pixel in
    # Python - deshalb auch bei grossen Bildern schnell.
    return im.point(lambda v: (v - lo) * scale)


def make_thumbnail(full_path):
    if not (HAVE_PIL and SHOW_THUMBNAILS):
        return None
    try:
        with Image.open(full_path) as im:
            im = _rescale_high_bitdepth(im)
            im = im.convert("RGB")
            im.thumbnail((THUMBNAIL_MAX_PX, THUMBNAIL_MAX_PX))
            buf = BytesIO()
            im.save(buf, format="JPEG", quality=72)
            b64 = base64.b64encode(buf.getvalue()).decode("ascii")
            return f"data:image/jpeg;base64,{b64}"
    except Exception:
        return None


class _ThumbnailTimeout(Exception):
    pass


def make_thumbnail_with_hard_timeout(full_path, timeout=THUMBNAIL_TIMEOUT_SECONDS):
    """Wie make_thumbnail(), aber mit einer vom Datei-I/O unabhaengigen
    Notbremse in einem Daemon-Thread (gleiches Muster wie
    _fetch_url_with_hard_timeout fuer die Online-Namensaufloesung).

    Wird der Timeout ueberschritten, wirft diese Funktion _ThumbnailTimeout
    - bewusst NICHT einfach None zurueckgeben, damit get_thumbnail_cached()
    das Ergebnis diesmal nicht in den Zwischenspeicher schreibt (ein
    voruebergehender Virenschutz-Stau soll nicht dauerhaft als "kein
    Vorschaubild moeglich" gecacht werden - beim naechsten Lauf wird die
    Datei also einfach erneut versucht)."""
    result = {}

    def worker():
        result["thumb"] = make_thumbnail(full_path)

    thread = threading.Thread(target=worker, daemon=True)
    thread.start()
    thread.join(timeout)
    if thread.is_alive():
        raise _ThumbnailTimeout(full_path)
    return result.get("thumb")


# ======================================================================
# Vorschaubild-Zwischenspeicher
# ======================================================================
# Ein Vorschaubild aus einem grossen TIFF/JPG zu erzeugen (oeffnen, ggf. auf
# 0-255 strecken, verkleinern, neu als JPEG kodieren) ist bei vielen
# Projekten der langsamste Teil des Laufs - und aendert sich fuer ein
# bereits fertiges Projekt normalerweise nie wieder. Deshalb wird das
# Ergebnis neben dem Skript/der .exe in einer JSON-Datei zwischengespeichert,
# geschluesselt ueber den vollen Pfad der gewaehlten Vorschaudatei; ein
# Eintrag wird nur dann wiederverwendet, wenn Aenderungszeit UND Groesse
# dieser Datei seit dem letzten Lauf identisch sind. Neue oder veraenderte
# Projekte werden also ganz normal neu erzeugt, unveraenderte Projekte
# sparen sich das erneute Oeffnen/Dekodieren der Bilddatei.

THUMB_CACHE_FILENAME = "AstroLogbuch_thumb_cache.json"


def load_thumb_cache(cache_path):
    try:
        with open(cache_path, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return {}


def save_thumb_cache(cache_path, cache):
    try:
        with open(cache_path, "w", encoding="utf-8") as f:
            json.dump(cache, f)
    except Exception:
        pass  # der Zwischenspeicher ist nur eine Optimierung, kein Muss


def get_thumbnail_cached(preview_path, size, mtime, old_cache, used_cache, stats, max_bytes=None):
    """size/mtime kommen von pick_preview_file() (letztlich aus dem
    urspruenglichen Verzeichnis-Listing in scan_project(), siehe dort) -
    bewusst kein eigener os.stat()-Aufruf mehr hier, das war vorher eine
    beobachtete Haenger-Quelle (siehe _scandir_walk-Kommentar).

    max_bytes (nur vom Vorschaubild-Auswahlfenster genutzt, siehe
    list_preview_candidates): ist die Datei bereits gecacht, wird das
    Ergebnis immer verwendet, unabhaengig von der Groesse. Nur fuer eine
    NEUE Generierung wird oberhalb dieser Grenze bewusst kein Thumbnail
    erzeugt (z. B. ein 400-MB-Linear-Master wuerde das Oeffnen des
    Auswahlfensters spuerbar verzoegern) - der Datei-Eintrag bleibt trotzdem
    per Namen waehlbar, nur ohne Live-Vorschau."""
    key = os.path.normcase(os.path.abspath(preview_path))
    old = old_cache.get(key)
    if old and old.get("mtime") == mtime and old.get("size") == size:
        used_cache[key] = old
        stats["hits"] += 1
        return old.get("thumb")
    if max_bytes is not None and size > max_bytes:
        stats["skipped_large"] = stats.get("skipped_large", 0) + 1
        return None
    try:
        thumb = make_thumbnail_with_hard_timeout(preview_path)
    except _ThumbnailTimeout:
        # Absichtlich NICHT in used_cache eintragen: beim naechsten Lauf
        # soll diese Datei erneut versucht werden, statt "kein Vorschaubild"
        # dauerhaft festzuschreiben (siehe make_thumbnail_with_hard_timeout).
        stats["timeout"] = stats.get("timeout", 0) + 1
        return None
    used_cache[key] = {"mtime": mtime, "size": size, "thumb": thumb}
    stats["new"] += 1
    return thumb


def resolve_camera_labels(all_scans):
    """Fasst Kamera-Rohtoken ueber ALLE Projekte hinweg zusammen.

    Steht MM oder MC explizit im Dateinamen, ist das pro Datei eindeutig
    und wird direkt uebernommen - unabhaengig davon, ob fuer dieselbe
    Modellnummer an anderer Stelle im Archiv auch die jeweils andere
    Variante vorkommt. Das ist dann kein Erkennungsproblem, sondern
    schlicht ein zweiter Kamerakoerper desselben Modells (z. B. ein Wechsel
    von Mono auf Farbe/OSC oder umgekehrt zu einem beliebigen Zeitpunkt).
    Beide erscheinen dann als eigene Zeile in der Kameranutzung.

    Nur wenn im Namen weder MM noch MC steht, ist die Variante fuer diese
    Aufnahmen tatsaechlich unbekannt. Dann wird aus der Filternutzung
    dieser namenlosen Aufnahmen geschaetzt (mit Filter -> eher Mono, ohne
    Filter -> eher Farbe/OSC) und das Ergebnis als 'vermutlich'
    gekennzeichnet - als eigene Zeile, nicht vermischt mit den sicheren
    Werten."""
    explicit_variants = {}   # Modellnummer -> Menge der explizit gefundenen Varianten (MM/MC)
    unlabeled_stats = {}     # Modellnummer -> Filter-Nutzung der Aufnahmen OHNE MM/MC im Namen

    for scan in all_scans:
        for cam_raw, v in scan["cameras"].items():
            model = extract_camera_model(cam_raw)
            ev = explicit_camera_variant(cam_raw)
            if ev:
                explicit_variants.setdefault(model, set()).add(ev)
            else:
                us = unlabeled_stats.setdefault(model, {"filtered": 0, "unfiltered": 0})
                us["filtered"] += v["filtered"]
                us["unfiltered"] += v["unfiltered"]

    def resolve(cam_raw):
        model = extract_camera_model(cam_raw)
        base = CAMERA_MAP.get(model.lower(), model)
        ev = explicit_camera_variant(cam_raw)
        if ev:
            variant = "Mono" if ev == "MM" else "Farbe/OSC"
            return f"{base} ({variant})"

        # Kein MM/MC im Namen dieser konkreten Aufnahme: schaetzen. Ist fuer
        # dieses Modell an anderer Stelle genau eine Variante explizit
        # bekannt, wird die uebernommen (weiterhin als 'vermutlich'
        # gekennzeichnet, da diese Datei selbst es nicht bestaetigt);
        # kommen beide vor oder keine, wird aus der eigenen Filternutzung
        # dieser unbeschrifteten Aufnahmen geschaetzt.
        variants = explicit_variants.get(model, set())
        if len(variants) == 1:
            variant = "Mono" if next(iter(variants)) == "MM" else "Farbe/OSC"
        else:
            us = unlabeled_stats.get(model, {"filtered": 0, "unfiltered": 0})
            variant = "Mono" if us["filtered"] >= us["unfiltered"] else "Farbe/OSC"
        return f"{base} ({variant}, vermutlich)"

    return resolve


def build_entry_from_scan(name, scan, project_path, ref_year, resolve_camera, merged_from=None,
                           group=None,
                           thumb_cache_old=None, thumb_cache_used=None, thumb_stats=None,
                           object_cache_old=None, object_cache_used=None, object_stats=None):
    # Kamera-Rohtoken auf die global aufgeloesten Labels ummappen (dabei
    # koennen mehrere Rohtoken im selben Projekt zu einem Label verschmelzen)
    merged_cams = {}
    for cam_raw, v in scan["cameras"].items():
        label = resolve_camera(cam_raw)
        e = merged_cams.setdefault(label, {"count": 0, "seconds": 0.0, "filtered": 0, "unfiltered": 0})
        e["count"] += v["count"]; e["seconds"] += v["seconds"]
        e["filtered"] += v["filtered"]; e["unfiltered"] += v["unfiltered"]
    scan = dict(scan)
    scan["cameras"] = merged_cams

    status, month_tag = detect_status(name, scan)
    hours, exact = total_hours(scan)
    nights = len(scan["dates_seen"]) or (1 if scan["total_files"] else 0)
    category = classify_category(name)
    coords = find_object_coords(
        name, category=category,
        online_cache_old=object_cache_old, online_cache_used=object_cache_used,
        online_stats=object_stats)
    obs = compute_obs(coords[0], coords[1], ref_year) if coords else None

    thumb = None
    if HAVE_PIL and SHOW_THUMBNAILS:
        # Manuelle Wahl (Klick auf das Vorschaubild, siehe Api.set_preview_override)
        # geht der automatischen Heuristik vor. Kein Eintrag fuer dieses Projekt
        # -> ganz normal die Heuristik (Normalfall). Eintrag None -> Nutzer hat
        # explizit "kein Bild" gewaehlt. Eintrag als Pfad -> genau diese Datei
        # verwenden, sofern sie noch existiert; ist sie verschwunden (geloescht/
        # umbenannt), faellt es automatisch auf die Heuristik zurueck statt
        # einfach kein Bild mehr zu zeigen.
        picked = None
        if project_path in PREVIEW_OVERRIDES:
            override_rel = PREVIEW_OVERRIDES[project_path]
            if override_rel is None:
                picked = None
            else:
                for rel, size, mtime in scan["final_files"]:
                    if rel == override_rel:
                        picked = (os.path.join(project_path, rel), size, mtime)
                        break
                if picked is None and scan["final_files"]:
                    picked = pick_preview_file(project_path, scan["final_files"])
        elif scan["final_files"]:
            picked = pick_preview_file(project_path, scan["final_files"])
        if picked:
            preview_path, preview_size, preview_mtime = picked
            if thumb_cache_old is not None and thumb_cache_used is not None:
                thumb = get_thumbnail_cached(
                    preview_path, preview_size, preview_mtime, thumb_cache_old, thumb_cache_used,
                    thumb_stats if thumb_stats is not None else {"hits": 0, "new": 0})
            else:
                try:
                    thumb = make_thumbnail_with_hard_timeout(preview_path)
                except _ThumbnailTimeout:
                    thumb = None

    note = f"Zusammengeführt mit: {', '.join(merged_from)}" if merged_from else ""

    return {
        "name": clean_display_name(name),
        "tag": month_tag,
        "category": category,
        "status": status,
        "nights": nights,
        "hours": hours,
        "hoursExact": exact,
        "filters": format_filters(scan),
        "cameras": format_cameras(scan),
        "camStats": {label: {"count": v["count"], "seconds": round(v["seconds"], 1)}
                     for label, v in scan["cameras"].items()},
        "note": note,
        "obs": obs,
        "thumb": thumb,
        "path": project_path,
        "bytes": scan["total_bytes"],
        "lastModified": scan["last_modified"] or None,
        "group": group,
    }


_SOLAR_SYSTEM_SIGNAL_CATEGORIES = ("Komet", "Mond", "Planet", "Konjunktion")


def _folder_name_has_own_signal(name):
    """Traegt der Ordnername selbst schon eines der Signale, auf die
    detect_status()/find_object_coords() weiter oben ohnehin zurueckgreifen
    (Done-/Fertig-Tag, Monatshinweis, Katalognummer oder ein Eintrag aus
    OBJECT_CATALOG)? Wenn ja, gilt dieser Ordner - wie im ganzen Programm
    ueblich - als EIN eigenstaendiges Projekt, unabhaengig davon, wie er
    intern aufgebaut ist. Nur wenn KEINES davon zutrifft, kommt ueberhaupt
    infrage, dass es sich um einen reinen Sammelordner handelt (siehe
    discover_project_folders() weiter unten).

    Sonnensystem-Objekte (Mars, Mond, Jupiter, Saturn, Venus, Kometen)
    haben KEINE feste Himmelsposition und stehen deshalb nie in
    OBJECT_CATALOG (siehe dort) und tragen so gut wie nie eine
    Katalognummer - ohne den Zusatzcheck ueber CATEGORY_KEYWORDS haette
    z. B. ein Sammelordner "Sonnensystem" mit Kindern "Mars", "Mond",
    "Jupiter_180619" NICHT als Sammelordner gegolten (kein Kind mit
    erkennbarem Signal), und waere faelschlich selbst als EIN Projekt
    gelistet worden."""
    lname = name.lower()
    if re.search(r'(?<![a-z0-9])(?:done|fertig)(?![a-z0-9])', lname):
        return True
    if has_month_hint(name):
        return True
    for pattern, _prefix in CATALOG_NUM_PATTERNS:
        if pattern.search(name):
            return True
    if any(key in lname for key in OBJECT_CATALOG):
        return True
    for cat, keywords in CATEGORY_KEYWORDS:
        if cat in _SOLAR_SYSTEM_SIGNAL_CATEGORIES and any(k in lname for k in keywords):
            return True
    return False


def _looks_like_grouping_folder(folder_name, subdirs):
    """subdirs: bereits um ausgeschlossene Namen bereinigte Liste von
    DirEntry-Objekten der direkten Unterordner. Bewusst KONSERVATIV: ein
    Ordner gilt nur dann als reiner Sammelordner (z. B. nach Montierung
    oder Kategorie sortiert), wenn ER SELBST kein eigenes Astro-Signal
    traegt UND mindestens zwei seiner Unterordner UNABHAENGIG VONEINANDER
    schon selbst ein solches Signal tragen (siehe
    _folder_name_has_own_signal()) - nur DAS ist ein hinreichend sicherer
    Beleg fuer "hier liegen mehrere echte, unterschiedliche Projekte
    nebeneinander".

    Eine fruehere, laxere Fassung hat stattdessen alles akzeptiert, was
    nicht wie ein reiner Datums-/Session-Ordner aussah - das hat sich an
    einem echten, langjaehrig gewachsenen Archiv als zu großzuegig
    erwiesen: interne Arbeitsordner eines EINZELNEN Projekts wie
    "Stack_PI", "CR_Stack"/"Non_CR_Stack" oder nach Brennweite/Sitzung
    benannte Unterordner ("1280mm - 21.01.23") wurden dabei faelschlich
    als eigene Projekte aufgesplittet. Mit der strengeren Regel bleiben
    solche Faelle unangetastet (kein Kind traegt fuer sich ein erkennbares
    Katalog-/Done-/Monats-Signal), waehrend z. B. ein Sammelordner mit
    "M51 ... OK fertig" und "NGC 6960 ... 08.09.2026" als Kindern weiterhin
    korrekt erkannt wird."""
    if _folder_name_has_own_signal(folder_name):
        return False
    signaled = [e for e in subdirs
                if not any(w in e.name.lower() for w in CALIB_WORDS)
                and not any(w in e.name.lower() for w in STACK_WORDS)
                and _folder_name_has_own_signal(e.name)]
    return len(signaled) >= 2


def _discover_projects_under(folder, group):
    """Rekursiver Kern von discover_project_folders() (siehe dort fuer den
    eigentlichen Einstiegspunkt). group ist der Name des naechstgelegenen
    umschliessenden Sammelordners (oder None, falls folder direkt unter
    dem gewaehlten Astro-Ordner liegt) - wird nur fuer die informative
    "Gruppe"-Anzeige im Dashboard mitgefuehrt, hat auf die Status-/
    Kategorie-Erkennung selbst keinen Einfluss (die bleibt wie bisher
    allein am Namen des gefundenen Projektordners selbst festgemacht)."""
    try:
        with os.scandir(folder) as it:
            subdirs = [e for e in it if e.is_dir(follow_symlinks=False)
                       and e.name.lower() not in EXCLUDE_FOLDER_NAMES]
    except OSError:
        subdirs = []

    if subdirs and _looks_like_grouping_folder(os.path.basename(folder), subdirs):
        results = []
        this_group = os.path.basename(folder)
        for e in sorted(subdirs, key=lambda x: x.name.lower()):
            lname = e.name.lower()
            if any(w in lname for w in CALIB_WORDS) or any(w in lname for w in STACK_WORDS):
                # Gemeinsame Kalibrierdaten des ganzen Sammelordners (z. B.
                # eine fuer alle Ziele genutzte darks/flats-Bibliothek einer
                # Montierung) oder ein interner Verarbeitungsordner - kein
                # eigenes Projekt, wird hier bewusst uebersprungen statt als
                # eigene (leere/verwirrende) Zeile zu erscheinen.
                continue
            results.extend(_discover_projects_under(e.path, this_group))
        return results

    return [(os.path.basename(folder), folder, group)]


def discover_project_folders(root_folder):
    """Findet die tatsaechlichen Projektordner unterhalb von root_folder.
    Im bisherigen (weiterhin haeufigsten) Fall ist bereits jeder direkte
    Unterordner von root_folder selbst ein Projekt - der Astro-Ordner
    selbst gilt dabei nie als Projekt, nur seine direkten Unterordner
    werden je einzeln betrachtet. Sieht ein solcher Unterordner dagegen
    wie ein reiner Sammelordner aus (z. B. nach Montierung oder Kategorie
    sortiert, ohne eigene Aufnahmen), wird automatisch eine Ebene tiefer
    nach den echten Projekten gesucht - und das rekursiv, beliebig tief
    (siehe _discover_projects_under()/_looks_like_grouping_folder()).

    Gibt eine Liste von (name, path, group)-Tripeln zurueck. name ist der
    eigene Ordnername des gefundenen Projekts (fuer Status-/Kategorie-
    Erkennung massgeblich, siehe detect_status() weiter oben), path
    dessen absoluter Pfad, group der Name des naechstgelegenen
    Sammelordners oder None."""
    try:
        with os.scandir(root_folder) as it:
            top = [e for e in it if e.is_dir(follow_symlinks=False)
                   and e.name.lower() not in EXCLUDE_FOLDER_NAMES]
    except OSError:
        return []
    results = []
    for e in sorted(top, key=lambda x: x.name.lower()):
        results.extend(_discover_projects_under(e.path, None))
    return results


def scan_root(root_folder, ref_year, thumb_cache_path=None, object_cache_path=None, progress_cb=None):
    """progress_cb(current, total, text), falls angegeben, wird zusaetzlich
    zum print() bei jedem Fortschrittsschritt aufgerufen (fuer den
    Splash-Screen im Programmfenster, siehe render_loading_page())."""
    # Phase 1: die tatsaechlichen Projektordner finden (siehe
    # discover_project_folders() oben) und einzeln einlesen. Schluessel ist
    # bewusst der absolute Pfad, nicht der blosse Ordnername: Bei
    # verschachtelten Sammelordnern (Montierung/Kategorie/...) koennten
    # sonst zwei Projekte mit zufaellig gleichem Namen in unterschiedlichen
    # Zweigen einander ueberschreiben.
    candidates = discover_project_folders(root_folder)

    total = len(candidates)
    entries = {}      # Pfad -> scan_project()-Ergebnis
    names = {}        # Pfad -> eigener Ordnername
    groups = {}        # Pfad -> Name des naechstgelegenen Sammelordners oder None
    order = []          # Pfade in Fundreihenfolge
    for i, (name, full, group) in enumerate(candidates, start=1):
        line = f"[{i}/{total}] Lese Ordner: {name}"
        print(line, flush=True)
        if progress_cb:
            progress_cb(i, total * 2, line)
        try:
            entries[full] = scan_project(full)
        except Exception:
            entries[full] = None
        names[full] = name
        groups[full] = group
        order.append(full)

    # Phase 2: MERGE_INTO anwenden (Quelle in Ziel einrechnen, Quelle entfernen).
    # MERGE_INTO ist ein reiner Handarbeits-Sonderfall (siehe Definition weiter
    # oben) und verweist auf Ordnernamen, nicht auf Pfade. Bei verschachtelten
    # Sammelordnern koennte derselbe Name mehrfach vorkommen - in dem seltenen
    # Fall wird die Zusammenfuehrung fuer diesen Namen sicherheitshalber
    # uebersprungen, statt versehentlich den falschen Zweig zu treffen.
    name_to_paths = {}
    for full, nm in names.items():
        name_to_paths.setdefault(nm, []).append(full)
    merged_from_map = {}
    for src, dst in MERGE_INTO.items():
        src_paths = name_to_paths.get(src, [])
        dst_paths = name_to_paths.get(dst, [])
        if len(src_paths) != 1 or len(dst_paths) != 1:
            continue
        src_path, dst_path = src_paths[0], dst_paths[0]
        if entries.get(src_path) is not None and entries.get(dst_path) is not None:
            merge_scans(entries[dst_path], entries[src_path])
            del entries[src_path]
            order.remove(src_path)
            merged_from_map.setdefault(dst_path, []).append(src)

    # Phase 3: Kamera-Modelle ueber alle verbliebenen Projekte hinweg aufloesen
    resolve_camera = resolve_camera_labels([s for s in entries.values() if s is not None])

    # Phase 4: fertige Zeilen bauen (inkl. Vorschaubilder – das ist meist der
    # langsamste Teil, deshalb hier eine eigene Fortschrittsanzeige)
    old_thumb_cache = load_thumb_cache(thumb_cache_path) if thumb_cache_path else {}
    used_thumb_cache = {}
    thumb_stats = {"hits": 0, "new": 0}

    old_object_cache = load_object_cache(object_cache_path) if object_cache_path else {}
    used_object_cache = {}
    object_stats = {"hits": 0, "new": 0, "notfound": 0, "failed": 0, "network_dead": False}

    projects = []
    total2 = len(order)
    for i, full in enumerate(order, start=1):
        name = names[full]
        line = f"[{i}/{total2}] Werte aus / erzeuge Vorschaubild: {name}"
        print(line, flush=True)
        if progress_cb:
            progress_cb(total + i, total * 2, line)
        scan = entries[full]
        if scan is None:
            projects.append({
                "name": clean_display_name(name), "tag": None, "category": "Sonstiges", "status": "unclear",
                "nights": None, "hours": None, "hoursExact": False,
                "filters": "Fehler beim Einlesen dieses Ordners", "cameras": "–", "camStats": {},
                "note": "", "obs": None, "thumb": None, "path": full, "bytes": 0, "lastModified": None,
                "group": groups.get(full),
            })
            continue
        try:
            projects.append(build_entry_from_scan(
                name, scan, full, ref_year, resolve_camera, merged_from_map.get(full),
                group=groups.get(full),
                thumb_cache_old=old_thumb_cache, thumb_cache_used=used_thumb_cache, thumb_stats=thumb_stats,
                object_cache_old=old_object_cache, object_cache_used=used_object_cache, object_stats=object_stats))
        except Exception:
            projects.append({
                "name": clean_display_name(name), "tag": None, "category": "Sonstiges", "status": "unclear",
                "nights": None, "hours": None, "hoursExact": False,
                "filters": "Fehler bei der Auswertung dieses Ordners", "cameras": "–", "camStats": {},
                "note": "", "obs": None, "thumb": None, "path": full, "bytes": 0, "lastModified": None,
                "group": groups.get(full),
            })

    if thumb_cache_path:
        save_thumb_cache(thumb_cache_path, used_thumb_cache)
        if thumb_stats["hits"] or thumb_stats["new"]:
            print(f"Vorschaubilder: {thumb_stats['hits']} aus Zwischenspeicher übernommen, "
                  f"{thumb_stats['new']} neu erzeugt.", flush=True)
        if thumb_stats.get("timeout"):
            print(f"Vorschaubilder: {thumb_stats['timeout']}x wegen Zeitüberschreitung "
                  f"übersprungen (vermutlich Virenschutz), Datei wird beim nächsten Lauf "
                  f"erneut versucht.", flush=True)

    if object_cache_path:
        save_object_cache(object_cache_path, used_object_cache)
        if object_stats["new"] or object_stats["notfound"]:
            print(f"Objekt-Koordinaten online abgefragt: {object_stats['new']} gefunden, "
                  f"{object_stats['notfound']} ohne Treffer.", flush=True)
        if object_stats["failed"]:
            print("Online-Namensauflösung war nicht erreichbar (kein Internet? Firewall?), "
                  "betroffene Objekte bleiben ohne optimales Fenster.", flush=True)
    return projects


# ======================================================================
# HTML-Dashboard
# ======================================================================

# Logo (Mondsichel-Emblem) als PNG, 256x256, base64-eingebettet: dient dem
# Splash-Screen im Programmfenster als Bild UND ist Quelle fuer
# AstroLogbuch.ico (Programm-/Fenstericon, siehe Schritt 2 in ANLEITUNG.txt).
APP_LOGO_PNG_BASE64 = (
    "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"
)


# Logo-Schriftzug (nur Text, dunkles abgerundetes Badge, aus demselben
# Logo herausgeschnitten wie APP_LOGO_PNG_BASE64) fuer die Kopfzeile des
# Dashboards, ersetzt dort den bisherigen reinen Text-Titel.
HEADER_LOGO_PNG_BASE64 = (
    "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"
)


HTML_TEMPLATE = r"""<!DOCTYPE html>
<html lang="de">
<head>
<meta charset="utf-8">
<title>AstroLogbuch</title>
<meta name="viewport" content="width=device-width, initial-scale=1">
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Fraunces:ital,opsz,wght@0,9..144,400;0,9..144,600;1,9..144,500&family=IBM+Plex+Sans:wght@400;500;600;700&family=IBM+Plex+Mono:wght@400;500;600&display=swap">
<style>
  :root{
    --bg:#f6f4ee; --surface:#ffffff; --surface-2:#eeece2; --surface-3:#e4e1d2;
    --border:#dbd6c6; --border-soft:#e8e4d6;
    --text:#20241f; --text-dim:#5c6156; --text-faint:#8b8f80;
    --accent:#a85a2b; --accent-soft:#f0dcc4;
    --good:#3c7a52; --good-soft:#dcead9;
    --warn:#a8791f; --warn-soft:#f2e6c8;
    --bad:#a13f34; --bad-soft:#f3ddd6;
    --neutral:#6b7280; --neutral-soft:#e7e6df;
    --shadow: 0 1px 2px rgba(30,25,10,.06), 0 8px 24px -12px rgba(30,25,10,.15);
    color-scheme: light;
  }
  @media (prefers-color-scheme: dark){
    :root:not([data-theme="light"]){
      --bg:#0d1119; --surface:#151b28; --surface-2:#1c2434; --surface-3:#253045;
      --border:#2b3548; --border-soft:#212a3a;
      --text:#e9ecf3; --text-dim:#a3acc2; --text-faint:#6f7996;
      --accent:#e4a15c; --accent-soft:#3a2d1c;
      --good:#6fc190; --good-soft:#16281f;
      --warn:#e4b95c; --warn-soft:#2f2717;
      --bad:#e2836f; --bad-soft:#2f1e1a;
      --neutral:#8892ab; --neutral-soft:#1c2230;
      --shadow: 0 1px 2px rgba(0,0,0,.4), 0 12px 32px -16px rgba(0,0,0,.6);
      color-scheme: dark;
    }
  }
  *{box-sizing:border-box;}
  body{ margin:0; background:var(--bg); color:var(--text); font-family:'IBM Plex Sans', system-ui, sans-serif; font-size:14.5px; line-height:1.5; }
  .num{ font-family:'IBM Plex Mono', ui-monospace, monospace; font-variant-numeric:tabular-nums; }
  /* Volle Breite bis 1600px (verhindert seitliches Scrollen bei schmaleren
     Fenstern), darueber hinaus zentriert mit fester Obergrenze - sonst
     ziehen sich Tabellenspalten auf sehr breiten Monitoren unschoen
     auseinander und es entsteht viel Leerraum innerhalb der Zellen statt
     eines cleanen Randes. */
  .wrap{ max-width:1600px; width:100%; margin:0 auto; padding:28px clamp(16px,2.2vw,40px) 60px; box-sizing:border-box; }
  header.top{ display:flex; justify-content:space-between; align-items:flex-end; gap:24px; flex-wrap:wrap; margin-bottom:20px; padding-bottom:16px; border-bottom:1px solid var(--border); }
  .brand-logo{ display:block; height:46px; width:auto; margin:2px 0; border-radius:10px; }
  .sub{ color:var(--text-dim); margin:8px 0 0; max-width:60ch; }
  .meta-block{ text-align:right; font-size:12.5px; color:var(--text-faint); }
  .meta-block b{ color:var(--text-dim); font-weight:600; }
  .stats{ display:grid; grid-template-columns:repeat(7,1fr); gap:9px; margin-bottom:16px; }
  @media (max-width:1100px){ .stats{ grid-template-columns:repeat(4,1fr);} }
  @media (max-width:640px){ .stats{ grid-template-columns:repeat(2,1fr);} }
  .stat{ background:var(--surface); border:1px solid var(--border-soft); border-radius:10px; padding:11px 14px; box-shadow:var(--shadow); }
  .stat .v{ font-family:'IBM Plex Mono',monospace; font-size:22px; font-weight:600; }
  .stat .l{ font-size:11.5px; color:var(--text-faint); text-transform:uppercase; letter-spacing:.06em; margin-top:2px; }
  .stat .v-sub{ font-size:11px; color:var(--text-faint); font-family:'IBM Plex Mono',monospace; margin-top:4px; }
  .stat.good .v{ color:var(--good); } .stat.warn .v{ color:var(--warn); } .stat.bad .v{ color:var(--bad); } .stat.accent .v{ color:var(--accent); }
  /* Statistik-Kacheln oben sind klickbar und filtern die Tabelle unten auf
     denselben Status (siehe #stats-Klick-Handler weiter unten). */
  .stat.clickable{ cursor:pointer; transition:border-color .12s ease, transform .12s ease; }
  .stat.clickable:hover{ border-color:var(--accent); }
  .stat.clickable:active{ transform:scale(0.98); }
  .stat.clickable.active{ border-color:var(--accent); border-width:2px; padding:10px 13px; box-shadow:0 0 0 1px var(--accent), var(--shadow); }
  .panel{ background:var(--surface); border:1px solid var(--border-soft); border-radius:12px; box-shadow:var(--shadow); overflow:hidden; }
  /* overflow:hidden (fuer die runden Ecken) legt zugleich den Bezugsrahmen
     fuer position:sticky in thead th fest, OHNE selbst zu scrollen - der
     "klebende" Tabellenkopf haette dadurch gar keinen Effekt mehr und
     wuerde beim Scrollen der Seite einfach mitwandern. Deshalb hier
     overflow:visible statt hidden, damit sticky sich stattdessen an der
     Seite selbst orientiert (siehe .tablewrap-Kommentar oben). Die runden
     Ecken des Panels bleiben durch die eigene border-radius des Panels
     optisch erhalten, nur das (kaum sichtbare) Abschneiden ueberstehender
     Ecken der ersten/letzten Tabellenzeile entfaellt. */
  .table-panel{ overflow:visible; }
  .now-panel{ padding:13px 16px; margin-bottom:12px; border-color:var(--accent); }
  .now-head{ display:flex; align-items:center; gap:8px; font-weight:600; font-size:13px; margin-bottom:8px; }
  .now-dot{ width:8px; height:8px; border-radius:50%; background:var(--accent); box-shadow:0 0 0 4px var(--accent-soft); flex:none; }
  .now-body{ display:flex; flex-wrap:wrap; gap:8px; }
  .now-card{ background:var(--bg); border:1px solid var(--border-soft); border-radius:8px; padding:7px 12px; font-size:12.5px; color:var(--text-dim); }
  .now-card b{ color:var(--text); font-weight:600; }
  .now-card .num{ color:var(--accent); }
  /* Nur die Objekt-Karten im "Jetzt gut zu erreichen"-Panel sind anklickbar
     (springen zur passenden Tabellenzeile), die Kameranutzung-Kacheln
     (dieselbe .now-card-Klasse, anderes Panel) nicht - deshalb eine
     eigene Klasse statt generell .now-card. */
  .now-card.jump{ cursor:pointer; transition:border-color .12s ease; }
  .now-card.jump:hover{ border-color:var(--accent); }
  @keyframes rowFlash{ 0%{ background:var(--accent-soft); } 100%{ background:transparent; } }
  tbody tr.row-flash{ animation:rowFlash 1.6s ease; }
  .controls{ display:flex; gap:14px; flex-wrap:wrap; align-items:center; padding:13px 16px; border-bottom:1px solid var(--border-soft); }
  /* Status- und Typ-Filter sind inhaltlich zwei getrennte Gruppen (jede fuer
     sich mit "Alle"-Chip); ohne sichtbare Trennung wirken sie wie eine
     einzige Liste. Beschriftung plus Trennlinie zwischen den Gruppen macht
     die Zweiteilung auf den ersten Blick klar. */
  .chip-group{ display:flex; align-items:center; gap:8px; flex-wrap:wrap; }
  .chip-group + .chip-group{ padding-left:14px; border-left:1px solid var(--border); }
  .chip-group-label{ font-family:'IBM Plex Mono',monospace; font-size:10.5px; letter-spacing:.08em; text-transform:uppercase; color:var(--text-faint); white-space:nowrap; }
  .chipset{ display:flex; gap:6px; flex-wrap:wrap; }
  .chip{ font-family:'IBM Plex Mono',monospace; font-size:12px; padding:5px 11px; border-radius:999px; border:1px solid var(--border); background:var(--surface-2); color:var(--text-dim); cursor:pointer; user-select:none; white-space:nowrap; }
  .chip:hover{ border-color:var(--accent); color:var(--text); }
  .chip.active{ background:var(--accent); border-color:var(--accent); color:var(--bg); font-weight:600; }
  /* Markiert im Monats-Umschalter des "gut zu erreichen"-Panels zusaetzlich
     den tatsaechlich aktuellen Kalendermonat (unabhaengig davon, welcher
     Monat gerade durchgeklickt/angezeigt wird). */
  .chip.now:not(.active){ border-color:var(--accent); color:var(--accent); }
  .search{ margin-left:auto; }
  .search input{ font-family:'IBM Plex Sans', sans-serif; font-size:13px; padding:7px 12px; border-radius:8px; border:1px solid var(--border); background:var(--surface-2); color:var(--text); width:220px; outline:none; }
  .search input:focus{ border-color:var(--accent); }

  /* Einstellungen: Zahnrad-Knopf im Header, Panel als Overlay darueber */
  .gear-btn{ margin-top:8px; width:34px; height:34px; border-radius:9px; border:1px solid var(--border);
    background:var(--surface); color:var(--text-dim); font-size:17px; cursor:pointer; line-height:1; }
  .gear-btn:hover{ border-color:var(--accent); color:var(--accent); }
  .overlay{ position:fixed; inset:0; background:rgba(10,10,8,.45); display:flex; align-items:flex-start;
    justify-content:center; padding:5vh 16px; z-index:50; overflow-y:auto; }
  .overlay[hidden]{ display:none; }
  .settings-panel{ background:var(--surface); border:1px solid var(--border); border-radius:14px;
    box-shadow:var(--shadow); width:100%; max-width:640px; padding:24px 26px 22px; }
  .settings-panel h2{ font-family:'Fraunces',Georgia,serif; font-size:21px; margin:0 0 4px; }
  .settings-panel .hint{ color:var(--text-faint); font-size:12.5px; margin:0 0 20px; }
  .settings-field{ margin-bottom:16px; }
  .settings-field label{ display:block; font-size:12px; font-weight:600; color:var(--text-dim);
    margin-bottom:5px; text-transform:uppercase; letter-spacing:.05em; }
  .settings-field .field-hint{ font-size:11.5px; color:var(--text-faint); margin-top:4px; }
  .settings-field input[type="text"], .settings-field input[type="number"], .settings-field textarea{
    width:100%; box-sizing:border-box; font-family:'IBM Plex Sans',sans-serif; font-size:13px;
    padding:8px 10px; border-radius:8px; border:1px solid var(--border); background:var(--surface-2);
    color:var(--text); outline:none; }
  .settings-field textarea{ min-height:52px; resize:vertical; font-family:'IBM Plex Mono',monospace; }
  .settings-field input:focus, .settings-field textarea:focus{ border-color:var(--accent); }
  .folder-row{ display:flex; gap:8px; }
  .folder-row input{ flex:1; }
  .btn{ font-family:'IBM Plex Sans',sans-serif; font-size:13px; font-weight:600; padding:8px 14px;
    border-radius:8px; border:1px solid var(--border); background:var(--surface-2); color:var(--text);
    cursor:pointer; white-space:nowrap; }
  .btn:hover{ border-color:var(--accent); color:var(--accent); }
  .btn.primary{ background:var(--accent); border-color:var(--accent); color:#fff; }
  .btn.primary:hover{ opacity:.9; color:#fff; }
  .btn.tiny{ padding:4px 9px; font-size:11.5px; }
  .checkbox-row{ display:flex; align-items:center; gap:8px; }
  .checkbox-row label{ margin:0; text-transform:none; letter-spacing:0; font-weight:500; font-size:13px; color:var(--text); }
  .map-table{ display:flex; flex-direction:column; gap:6px; }
  .map-row{ display:grid; grid-template-columns:1fr 1fr auto; gap:8px; align-items:center; }
  .map-row input{ font-family:'IBM Plex Mono',monospace; font-size:12.5px; padding:6px 9px;
    border-radius:7px; border:1px solid var(--border); background:var(--surface-2); color:var(--text); outline:none; }
  .map-row input:focus{ border-color:var(--accent); }
  .settings-actions{ display:flex; justify-content:space-between; align-items:center; gap:12px; margin-top:22px; padding-top:16px; border-top:1px solid var(--border-soft); }
  .settings-status{ font-size:12.5px; color:var(--text-faint); flex:1; }
  .settings-status.err{ color:var(--bad); }
  .settings-status.ok{ color:var(--good); }
  .settings-fallback-note{ background:var(--warn-soft); border:1px solid var(--warn); color:var(--warn); border-radius:8px; padding:10px 12px; font-size:12.5px; margin-bottom:16px; }

  /* table-layout:fixed statt des Standards "auto": Bei "auto" verteilt der
     Browser bei width:100% ungenutzten Platz nach eigenen Regeln auf die
     Spalten - schmale Spalten (Status, Nächte, ...) konnten dadurch viel
     breiter werden als ihr Inhalt braucht (sichtbar als grosse Luecke
     zwischen Wert und naechster Spalte), waehrend textreiche Spalten
     (Filter/Aufnahmen, Kamera, Optimales Fenster) trotz eines zusaetzlichen
     max-width auf ihrem Inhalt unnoetig frueh umbrechen mussten. Mit
     "fixed" bestimmt stattdessen die <colgroup> unten die tatsaechliche
     Breite jeder Spalte, fest zugeschnitten auf ihren jeweiligen Inhalt. */
  table{ width:100%; border-collapse:collapse; table-layout:fixed; }
  /* Bewusst KEIN white-space:nowrap mehr hier: Das passte bei der
     ehemaligen Spaltenbreite "nach Inhalt" (table-layout:auto), bei den
     jetzt festen, teils schmaleren Spalten (siehe colgroup) wuerde eine
     lange Beschriftung wie "Letzte Bearbeitung" sonst einfach abgeschnitten
     statt in eine zweite Zeile umzubrechen. */
  thead th{ position:sticky; top:0; background:var(--surface-2); text-align:center; font-size:11px; text-transform:uppercase; letter-spacing:.06em; color:var(--text-faint); font-weight:600; padding:8px 12px; border-bottom:1px solid var(--border); cursor:pointer; }
  thead th:hover{ color:var(--text); }
  tbody td{ padding:7px 9px; border-bottom:1px solid var(--border-soft); vertical-align:top; text-align:center; }
  tbody tr:hover{ background:var(--surface-2); }
  tbody tr:last-child td{ border-bottom:none; }
  /* Bewusst KEIN overflow (weder x noch y) mehr auf .tablewrap: Jede
     Achse, die hier auf etwas anderes als "visible" gesetzt wird, zwingt
     laut CSS-Spezifikation (Kompatibilitaetsregel) automatisch AUCH die
     andere Achse von "visible" auf "auto" - ein reines "overflow-x:auto"
     fuehrte also durch die Hintertuer denselben verschachtelten
     Vertikal-Scrollbalken wieder ein, den dieser Umbau eigentlich
     beseitigen sollte. Ohne jegliches overflow hier scrollt jetzt
     ausschliesslich die ganze Seite (auch horizontal, falls die Tabelle
     bei einem sehr schmalen Fenster breiter als der Inhalt ist) - nur ein
     einziger Satz Scrollbalken, und der "klebende" Tabellenkopf
     (thead th{position:sticky}) haengt sich dadurch korrekt an die Seite
     selbst statt an einen inneren Container. */
  /* Kopf UND Wert bewusst gleich ausgerichtet (mittig): bei
     table-layout:auto verteilt der Browser bei width:100% ungenutzten Platz
     auf die Spalten, eine schmale Spalte (z. B. "Nächte") kann dadurch
     deutlich breiter werden, als ihr Inhalt braucht. Waeren Kopf und Wert
     unterschiedlich ausgerichtet (z. B. Kopf mittig, Wert rechtsbuendig),
     wuerden sie in so einer breiten Spalte sichtbar auseinanderklaffen,
     obwohl beide im selben Spaltenbereich liegen. Mittig fuer beide
     schliesst diese Luecke unabhaengig von der tatsaechlichen Spaltenbreite. */
  td.num-col, th.num-col{ text-align:center; font-family:'IBM Plex Mono',monospace; }
  /* Kurze badge-artige Werte (Typ-Kuerzel, Status-Pille) ebenfalls mittig,
     aus demselben Grund wie bei num-col oben - nur ohne die Monospace-
     Schrift, die dort speziell fuer Zahlen/Daten gedacht ist. */
  td.ctr-col, th.ctr-col{ text-align:center; }
  .obj{ font-weight:600; }
  .obj-link{ font-weight:600; color:var(--text); }
  tbody tr.row-link{ cursor:pointer; }
  tbody tr.row-link:hover .obj-link{ color:var(--accent); }
  .copy-toast{ position:fixed; left:50%; bottom:28px; transform:translateX(-50%) translateY(8px); background:var(--text); color:var(--bg); padding:9px 16px; border-radius:8px; font-size:12.5px; font-family:'IBM Plex Mono',monospace; opacity:0; pointer-events:none; transition:opacity .15s ease, transform .15s ease; box-shadow:var(--shadow); z-index:50; max-width:min(90vw,70ch); overflow:hidden; text-overflow:ellipsis; white-space:nowrap; }
  .copy-toast.show{ opacity:1; transform:translateX(-50%) translateY(0); }
  .obj-sub{ display:block; font-size:12px; color:var(--text-faint); font-weight:400; margin-top:1px; }
  /* border-radius:999px statt eines kleinen festen Wertes: die Typ-Spalte
     ist schmal genug, dass laengere Kategorien (z. B. "Nebel/Deep-Sky")
     zweizeilig umbrechen - bei einer festen kleinen Rundung wirkt eine so
     hoehere Box schnell eckig statt wie die Pillenform bei Status. 999px
     ergibt unabhaengig von der Hoehe (ein- oder zweizeilig) immer eine
     durchgehend abgerundete Kapselform, genau wie .pill. */
  .cat{ display:inline-block; font-size:11px; padding:2px 7px; border-radius:999px; background:var(--surface-3); color:var(--text-dim); font-family:'IBM Plex Mono',monospace; }
  .pill{ display:inline-flex; align-items:center; gap:5px; font-size:12px; font-weight:600; padding:3px 9px; border-radius:999px; white-space:nowrap; }
  .pill .dot{ width:6px; height:6px; border-radius:50%; }
  .pill.done{ background:var(--good-soft); color:var(--good); } .pill.done .dot{ background:var(--good); }
  .pill.open{ background:var(--warn-soft); color:var(--warn); } .pill.open .dot{ background:var(--warn); }
  .pill.unclear{ background:var(--bad-soft); color:var(--bad); } .pill.unclear .dot{ background:var(--bad); }
  .pill.neutral{ background:var(--neutral-soft); color:var(--neutral); } .pill.neutral .dot{ background:var(--neutral); }
  .none{ color:var(--text-faint); }
  /* Kein max-width mehr hier: die Spaltenbreite kommt jetzt fest aus der
     <colgroup> (table-layout:fixed), ein zusaetzlicher Cap hier wuerde nur
     wieder unnoetig frueh umbrechen, egal wie viel Platz die Spalte
     tatsaechlich hat. */
  .filters-txt{ font-size:12px; color:var(--text-dim); white-space:normal; overflow-wrap:break-word; }
  .obs-cell{ font-size:12px; color:var(--text-dim); white-space:normal; overflow-wrap:break-word; }
  .obs-cell .peak{ color:var(--text); font-weight:600; }
  .obs-badge{ display:inline-block; width:6px; height:6px; border-radius:50%; background:var(--good); margin-right:5px; }
  .obs-na{ font-size:12px; color:var(--text-faint); font-style:italic; }
  .merge-note{ display:block; font-size:11px; color:var(--text-faint); font-style:italic; margin-top:2px; }
  /* Vorschaubild fuellt die tatsaechliche Zeilenhoehe: height:100% bezieht
     sich auf die von den anderen Spalten vorgegebene Zeilenhoehe (durch
     Tabellenlayout aufgeloest), min-/max-height verhindern ein zu
     winziges oder zu riesiges Bild bei sehr kurzen bzw. sehr langen
     Zeilen. */
  /* Feste quadratische Groesse fuer alle Vorschaubilder, object-fit:cover
     schneidet dafuer einen mittigen Ausschnitt zu - so wirkt die Liste
     einheitlich, unabhaengig vom Seitenverhaeltnis des Originalbilds. */
  .thumb{ display:block; width:88px; height:88px; border-radius:6px; object-fit:cover; border:1px solid var(--border-soft); }
  .thumb-ph{ display:flex; width:88px; height:88px; border-radius:6px; background:var(--surface-3); align-items:center; justify-content:center; color:var(--text-faint); font-size:19px; }
  th.img-col, td.img-col{ width:100px; padding-right:4px; padding-left:14px; vertical-align:middle; }
  td.img-col{ cursor:pointer; }
  .preview-picker-grid{ display:grid; grid-template-columns:repeat(auto-fill,minmax(120px,1fr)); gap:10px;
    max-height:60vh; overflow-y:auto; margin-top:14px; }
  .preview-picker-item{ cursor:pointer; border:2px solid var(--border); border-radius:10px; padding:6px;
    background:var(--surface-2); text-align:center; }
  .preview-picker-item:hover{ border-color:var(--accent); }
  .preview-picker-item.active{ border-color:var(--accent); box-shadow:0 0 0 2px var(--accent) inset; }
  .preview-picker-item img{ display:block; width:100%; height:90px; object-fit:cover; border-radius:6px; }
  .preview-picker-item .ph{ display:flex; width:100%; height:90px; border-radius:6px; background:var(--surface-3);
    align-items:center; justify-content:center; color:var(--text-faint); font-size:24px; }
  .preview-picker-item .lbl{ font-size:11px; color:var(--text-dim); margin-top:5px; word-break:break-all; }
  tbody td:nth-child(2){ max-width:210px; overflow-wrap:break-word; }
  footer.legend{ margin-top:14px; font-size:12px; color:var(--text-faint); max-width:90ch; }
  .count-note{ padding:10px 18px; font-size:12px; color:var(--text-faint); border-top:1px solid var(--border-soft); }
</style>
</head>
<body>
<div class="wrap">
  <header class="top">
    <div>
      <img class="brand-logo" src="data:image/png;base64,%%HEADER_LOGO_B64%%" alt="AstroLogbuch">
      <p class="sub">Automatisch erzeugt: Status, Nächte, Belichtungszeiten und optimales Beobachtungsfenster je Projekt, direkt aus dem Ordner gelesen.</p>
    </div>
    <div class="meta-block">
      <div>%%ROOT_FOLDER%% &middot; Lokaler Scan</div>
      <div><b>Stand:</b> %%TIMESTAMP%%</div>
      <div>Standort: %%LATITUDE%%&deg; N</div>
      <div>AstroLogbuch v%%APP_VERSION%%</div>
      <button class="gear-btn" id="settingsBtn" title="Einstellungen">&#9881;</button>
    </div>
  </header>

  <div class="overlay" id="settingsOverlay" hidden>
    <div class="settings-panel">
      <h2>Einstellungen</h2>
      <p class="hint">Gilt für diesen Rechner und wird dauerhaft gespeichert (AstroLogbuch_config.json). Beim Speichern wird der Ordner sofort neu eingelesen.</p>
      <div id="settingsFallbackNote" class="settings-fallback-note" hidden>
        Einstellungen bearbeiten geht nur in der App-Ansicht (nicht im Browser-Fallback).
        Installiere pywebview und starte AstroLogbuch neu, oder bearbeite
        AstroLogbuch_config.json direkt mit einem Texteditor.
      </div>
      <div id="settingsForm">
        <div class="settings-field">
          <label>Astro-Ordner</label>
          <div class="folder-row">
            <input type="text" id="cfgRootFolder" readonly>
            <button class="btn" id="pickFolderBtn" type="button">Ordner wählen&hellip;</button>
          </div>
        </div>
        <div class="settings-field">
          <label>Standort (Breitengrad, Grad Nord)</label>
          <input type="number" step="0.01" id="cfgLatitude">
          <div class="folder-row" style="margin-top:8px;">
            <input type="text" id="cfgPlaceName" placeholder="Ort eingeben, z. B. Zürich (optional, statt Breitengrad von Hand)">
            <button class="btn" id="lookupPlaceBtn" type="button">Koordinate suchen</button>
          </div>
          <p class="field-hint" id="placeLookupStatus"></p>
        </div>
        <div class="settings-field">
          <div class="checkbox-row"><input type="checkbox" id="cfgOnlineLookup"><label for="cfgOnlineLookup">Unbekannte Objekte online nachschlagen (Sesame/CDS)</label></div>
          <div class="checkbox-row" style="margin-top:6px;"><input type="checkbox" id="cfgShowThumbnails"><label for="cfgShowThumbnails">Vorschaubilder anzeigen</label></div>
        </div>
        <div class="settings-field">
          <label>Kamera-Bezeichnungen</label>
          <p class="field-hint">Rohcode aus dem Dateinamen (z. B. "2600") &rarr; sprechender Name (z. B. "ASI2600"). Für andere Aufnahmesysteme frei anpassbar.</p>
          <div class="map-table" id="cameraMapTable"></div>
          <button class="btn tiny" id="addCameraRowBtn" type="button" style="margin-top:8px;">+ Zeile</button>
        </div>
        <div class="settings-field">
          <label>Filter-Bezeichnungen</label>
          <p class="field-hint">Kürzel aus dem Dateinamen (z. B. "H") &rarr; sprechender Name (z. B. "Ha").</p>
          <div class="map-table" id="filterMapTable"></div>
          <button class="btn tiny" id="addFilterRowBtn" type="button" style="margin-top:8px;">+ Zeile</button>
        </div>
        <div class="settings-field">
          <label>Ausgeschlossene Ordner</label>
          <p class="field-hint">Kommagetrennt. Diese Ordnernamen zählen nie als eigenes Projekt.</p>
          <textarea id="cfgExcludeFolders"></textarea>
        </div>
        <div class="settings-field">
          <label>Kalibrier-Schlüsselwörter</label>
          <p class="field-hint">Kommagetrennt. Ordner, deren Name eines dieser Wörter enthält, gelten als Flats/Darks/Bias und zählen nicht als Fortschritt.</p>
          <textarea id="cfgCalibWords"></textarea>
        </div>
      </div>
      <div class="settings-actions">
        <span class="settings-status" id="settingsStatus"></span>
        <button class="btn" id="cancelSettingsBtn" type="button">Abbrechen</button>
        <button class="btn primary" id="saveSettingsBtn" type="button">Speichern &amp; neu einlesen</button>
      </div>
    </div>
  </div>
  <div class="overlay" id="previewPickerOverlay" hidden>
    <div class="settings-panel" style="max-width:720px;">
      <h2>Vorschaubild wählen</h2>
      <p class="hint" id="previewPickerHint"></p>
      <div id="previewPickerGrid" class="preview-picker-grid"></div>
      <div class="settings-actions">
        <button class="btn" id="closePreviewPickerBtn" type="button">Abbrechen</button>
      </div>
    </div>
  </div>
  <div class="stats" id="stats"></div>
  <div class="panel now-panel" id="camPanel">
    <div class="now-head"><span class="now-dot" style="background:var(--text-dim);box-shadow:0 0 0 4px var(--surface-3);"></span><span>Kameranutzung gesamt</span></div>
    <div class="now-body" id="camBody"></div>
  </div>
  <div class="panel now-panel" id="nowPanel" style="display:none;">
    <div class="now-head"><span class="now-dot"></span><span id="nowHeadText"></span></div>
    <div style="display:flex; align-items:center; justify-content:space-between; gap:12px; flex-wrap:wrap; margin-bottom:10px;">
      <div class="chipset" id="monthChips"></div>
      <div class="checkbox-row" style="flex-shrink:0;"><input type="checkbox" id="hideFinishedNow" checked><label for="hideFinishedNow">Fertige Projekte ausblenden</label></div>
    </div>
    <div class="now-body" id="nowBody"></div>
  </div>
  <div class="panel table-panel">
    <div class="controls">
      <div class="chip-group">
        <span class="chip-group-label">Status</span>
        <div class="chipset" id="statusChips"></div>
      </div>
      <div class="chip-group">
        <span class="chip-group-label">Typ</span>
        <div class="chipset" id="catChips"></div>
      </div>
      <div class="search"><input id="searchBox" type="text" placeholder="Objekt suchen..."></div>
    </div>
    <div class="tablewrap">
      <table>
        <colgroup>
          <col style="width:100px;">
          <col style="width:calc((100% - 630px) * 0.30);">
          <col style="width:130px;">
          <col style="width:110px;">
          <col style="width:130px;">
          <col style="width:70px;">
          <col style="width:90px;">
          <col style="width:calc((100% - 630px) * 0.25);">
          <col style="width:calc((100% - 630px) * 0.20);">
          <col style="width:calc((100% - 630px) * 0.25);">
        </colgroup>
        <thead><tr>
          <th class="img-col"></th>
          <th data-key="name">Objekt</th>
          <th data-key="category" class="ctr-col">Typ</th>
          <th data-key="statusSort" class="ctr-col">Status</th>
          <th data-key="lastModified" class="num-col">Letzte Bearbeitung</th>
          <th data-key="nights" class="num-col">Nächte</th>
          <th data-key="hours" class="num-col">Std. gesamt</th>
          <th data-key="filters">Filter / Aufnahmen</th>
          <th data-key="cameras">Kamera</th>
          <th data-key="obsSort">Optimales Fenster</th>
        </tr></thead>
        <tbody id="rows"></tbody>
      </table>
    </div>
    <div class="count-note" id="countNote"></div>
  </div>
  <footer class="legend">
    <b>Fertig</b> = ausschliesslich bei "done" im Ordnernamen. <b>In Arbeit</b> = fertige Bilddatei gefunden, aber (noch)
    kein "done" im Namen. <b>Geplant</b> = Monatsname im Ordnernamen, aber sonst nichts für das Dashboard Auswertbares gefunden
    (der Ordner kann trotzdem Daten enthalten, z.&nbsp;B. Kalibrieraufnahmen oder ein Format, das nicht erkannt wird - "Geplant"
    bezieht sich nur auf den fehlenden Fortschritt, nicht auf die Ordnergrösse). <b>Nur Rohdaten</b> = nur Light-Frames, kein Stack.
    <b>Unklar</b> = Stack vorhanden, kein Endbild. <b>Kaum begonnen</b> = fast keine Dateien.<br><br>
    Std. gesamt: nur wenn im Unterordnernamen (z.&nbsp;B. "..._8.3h") oder im ASIAIR/NINA-Dateinamen eine Belichtungszeit steht;
    sonst bewusst leer statt geschätzt. Kamera: aus dem Dateinamen-Feld vor "gainXXX" gelesen (Kurzcode, z.&nbsp;B. "2600"); eigene
    Namen dafür in den Einstellungen (Zahnrad oben rechts) hinterlegbar. Flats/Darks/Bias zählen nirgends in die Belichtungszeit hinein.
    Optimales Fenster: Näherung für %%LATITUDE%%&deg; Nord, über eingebaute Kataloge und ggf. Online-Namensauflösung ermittelt
    (siehe ANLEITUNG.txt), nicht für jedes Objekt verfügbar (u.&nbsp;a. nie für Kometen);
    Wetter, Mond und Horizonthindernisse sind nicht berücksichtigt. Bild: Vorschau aus einer vorhandenen fertigen Datei
    (jpg/png/tif), keine KI-generierte Darstellung; bei mehreren Kandidaten wird die Datei mit der grössten Pixelfläche
    gewählt und Namen mit "Screenshot" o.&nbsp;ä. werden gemieden. Ohne passende Datei oder ohne installiertes Pillow
    bleibt ein Platzhalter.
    Kamera-Variante (Mono/Farbe): steht "MM" oder "MC" im Dateinamen, ist es sicher; sonst aus der Filternutzung hergeleitet
    und als "vermutlich" markiert. Ordner, die über MERGE_INTO zusammengeführt wurden, sind unter dem Objektnamen vermerkt.
    Klick auf eine Zeile öffnet den Ordner direkt im Explorer, solange dieses Programm noch läuft (es bedient das
    Dashboard dafür über eine lokale Adresse). Wird die Datei AstroLogbuch.html später erneut
    geöffnet, ohne dass das Programm läuft, wird ersatzweise nur der Pfad in die Zwischenablage kopiert. Vorschaubild:
    feste quadratische Grösse, es wird ein mittiger Ausschnitt gezeigt.
    Datenmenge (unter den Kacheln oben): tatsächliche Dateigrösse auf der Platte je Projekt bzw. Status, inklusive
    Kalibrieraufnahmen (Flats/Darks/Bias), falls vorhanden - diese werden für die eigentliche Auswertung zwar
    übersprungen (siehe "Geschwindigkeit"), ihr Speicherplatz zählt aber trotzdem mit.
  </footer>
</div>
<script>
const DATA = %%DATA_JSON%%;

const STATUS_META = {
  "done":        {label:"Fertig",        cls:"done",    sort:0},
  "wip":         {label:"In Arbeit",     cls:"open",    sort:1},
  "open-date":   {label:"Geplant",       cls:"open",    sort:2},
  "raw-only":    {label:"Nur Rohdaten",  cls:"unclear", sort:3},
  "unclear":     {label:"Unklar",        cls:"unclear", sort:4},
  "barely":      {label:"Kaum begonnen", cls:"neutral", sort:5},
};
const MONTHS_DE = ["Jan","Feb","Mär","Apr","Mai","Jun","Jul","Aug","Sep","Okt","Nov","Dez"];
let state = { status:"all", cat:"all", q:"", sortKey:"lastModified", sortDir:-1, previewMonth: new Date().getMonth()+1, hideFinishedNow:true };

// Ein reiner file://-Link wuerde in Chrome & Co. nur eine Dateiliste im
// Browser selbst zeigen, nie den echten Windows-Explorer. Solange dieses
// Programm aber laeuft, bedient es das Dashboard ueber einen kleinen
// lokalen Server (siehe main() im Python-Teil) - ein Klick auf eine Zeile
// fragt dort per fetch("/open?...") nach, und das Programm oeffnet den
// Ordner dann selbst mit os.startfile(). Nur falls das fehlschlaegt (z. B.
// weil die AstroLogbuch.html-Datei spaeter direkt per Doppelklick ohne
// laufendes Programm geoeffnet wurde), wird ersatzweise der Pfad in die
// Zwischenablage kopiert.
function copyToClipboard(text){
  const fallback = () => {
    const ta = document.createElement("textarea");
    ta.value = text; ta.style.position = "fixed"; ta.style.opacity = "0";
    document.body.appendChild(ta); ta.focus(); ta.select();
    try{ document.execCommand("copy"); }catch(e){}
    document.body.removeChild(ta);
  };
  if(navigator.clipboard && navigator.clipboard.writeText){
    navigator.clipboard.writeText(text).catch(fallback);
  } else {
    fallback();
  }
}
let toastEl = null, toastTimer = null;
function showToast(text){
  if(!toastEl){
    toastEl = document.createElement("div");
    toastEl.className = "copy-toast";
    document.body.appendChild(toastEl);
  }
  toastEl.textContent = text;
  toastEl.classList.add("show");
  clearTimeout(toastTimer);
  toastTimer = setTimeout(()=>toastEl.classList.remove("show"), 2600);
}
function openFolder(path){
  fetch("/open?path=" + encodeURIComponent(path))
    .then(res => {
      if(!res.ok) throw new Error("open failed");
      showToast("Ordner geöffnet: " + path);
    })
    .catch(() => {
      copyToClipboard(path);
      showToast("Konnte den Ordner nicht automatisch öffnen (Programm läuft nicht mehr?) - Pfad stattdessen kopiert: " + path);
    });
}

function inWindow(m, start, end){ if(start<=end) return m>=start && m<=end; return m>=start || m<=end; }

function fmtObsCell(d){
  const o = d.obs;
  if(!o) return '<span class="none">&ndash;</span>';
  const now = new Date().getMonth()+1;
  const active = inWindow(now, o.winStart, o.winEnd);
  const rangeTxt = `${MONTHS_DE[o.winStart-1]}&ndash;${MONTHS_DE[o.winEnd-1]}`;
  return `<span class="obs-cell">${active?'<span class="obs-badge" title="aktuell im Fenster"></span>':''}${rangeTxt} &middot; Höhepunkt <span class="peak">${o.peak}</span> (${o.alt}&deg;${o.cp?' &middot; zirkumpolar':''})</span>`;
}
function obsSortValue(d){
  if(!d.obs) return 99;
  const now = new Date().getMonth()+1;
  let dist = d.obs.winStart - now; if(dist<0) dist+=12;
  return dist;
}
function fmtHours(d){
  if(d.hours==null) return '<span class="none">&ndash;</span>';
  return `<span>${d.hoursExact?'':'~'}${d.hours}</span> h`;
}
function fmtLastModified(d){
  if(!d.lastModified) return '<span class="none">&ndash;</span>';
  const dt = new Date(d.lastModified*1000);
  const pad = n => String(n).padStart(2,"0");
  return `${pad(dt.getDate())}.${pad(dt.getMonth()+1)}.${dt.getFullYear()}`;
}
function fmtBytes(b){
  if(!b) return "0 GB";
  const units = ["B","KB","MB","GB","TB"];
  let i=0, v=b;
  while(v>=1024 && i<units.length-1){ v/=1024; i++; }
  return `${v>=100?Math.round(v):v.toFixed(1)} ${units[i]}`;
}

function render(){
  const statusCounts = {};
  DATA.forEach(d=>statusCounts[d.status]=(statusCounts[d.status]||0)+1);
  const cats = [...new Set(DATA.map(d=>d.category))].sort();
  const totalHours = DATA.reduce((s,d)=>s+(d.hours||0),0);
  const done = DATA.filter(d=>d.status==="done").length;
  const wip = DATA.filter(d=>d.status==="wip").length;
  const open = DATA.filter(d=>d.status==="open-date").length;
  // "Status unklar" fasst alles zusammen, was weder fertig, in Arbeit noch
  // mit Termin versehen ist (Nur Rohdaten, Unklar, Kaum begonnen) - so
  // ergeben alle vier Status-Kacheln zusammen immer die Gesamtzahl.
  const unclear = DATA.filter(d=>d.status==="unclear"||d.status==="raw-only"||d.status==="barely").length;

  // Datenmenge (Dateigroesse auf der Platte) je Status aufsummieren, damit
  // neben der Projektanzahl auch sichtbar ist, wo das meiste Volumen liegt.
  const bytesByStatus = {};
  DATA.forEach(d=>{ bytesByStatus[d.status] = (bytesByStatus[d.status]||0) + (d.bytes||0); });
  const totalBytes = DATA.reduce((s,d)=>s+(d.bytes||0),0);
  const doneBytes = bytesByStatus["done"]||0;
  const wipBytes = bytesByStatus["wip"]||0;
  const openBytes = bytesByStatus["open-date"]||0;
  const unclearBytes = (bytesByStatus["unclear"]||0)+(bytesByStatus["raw-only"]||0)+(bytesByStatus["barely"]||0);

  const statTileClass = key => "stat clickable" + (state.status===key ? " active" : "");
  document.getElementById("stats").innerHTML = `
    <div class="${statTileClass("all")}" data-stat-status="all"><div class="v">${DATA.length}</div><div class="l">Projekte gesamt</div><div class="v-sub">${fmtBytes(totalBytes)}</div></div>
    <div class="${statTileClass("done")} good" data-stat-status="done"><div class="v">${done}</div><div class="l">Fertig</div><div class="v-sub">${fmtBytes(doneBytes)}</div></div>
    <div class="${statTileClass("wip")} warn" data-stat-status="wip"><div class="v">${wip}</div><div class="l">In Arbeit</div><div class="v-sub">${fmtBytes(wipBytes)}</div></div>
    <div class="${statTileClass("open-date")} warn" data-stat-status="open-date"><div class="v">${open}</div><div class="l">Geplant</div><div class="v-sub">${fmtBytes(openBytes)}</div></div>
    <div class="${statTileClass("unclear-group")} bad" data-stat-status="unclear-group"><div class="v">${unclear}</div><div class="l">Status unklar</div><div class="v-sub">${fmtBytes(unclearBytes)}</div></div>
    <div class="stat accent"><div class="v">${Math.round(totalHours)}<span style="font-size:14px">h</span></div><div class="l">Dokumentierte Zeit</div><div class="v-sub">&nbsp;</div></div>
    <div class="stat"><div class="v">${DATA.reduce((s,d)=>s+(d.nights||0),0)}</div><div class="l">Aufnahmenächte</div><div class="v-sub">&nbsp;</div></div>`;

  const statusChipDefs = [["all","Alle"],["done","Fertig"],["wip","In Arbeit"],["open-date","Geplant"],["raw-only","Rohdaten"],["unclear","Unklar"],["barely","Kaum begonnen"]];
  document.getElementById("statusChips").innerHTML = statusChipDefs.map(([key,label])=>{
    const active = state.status===key ? "active":"";
    const n = key==="all" ? DATA.length : (statusCounts[key]||0);
    return `<span class="chip ${active}" data-status="${key}">${label} <span class="num">${n}</span></span>`;
  }).join("");
  document.getElementById("catChips").innerHTML = ["all",...cats].map(c=>{
    const active = state.cat===c ? "active":"";
    return `<span class="chip ${active}" data-cat="${c}">${c==="all"?"Alle Typen":c}</span>`;
  }).join("");

  let rows = DATA.filter(d=>{
    if(state.status==="unclear-group"){
      if(!(d.status==="unclear"||d.status==="raw-only"||d.status==="barely")) return false;
    } else if(state.status!=="all" && d.status!==state.status){
      return false;
    }
    if(state.cat!=="all" && d.category!==state.cat) return false;
    if(state.q && !(d.name.toLowerCase().includes(state.q))) return false;
    return true;
  });
  rows = rows.map(d=>({...d, statusSort: STATUS_META[d.status].sort, obsSort: obsSortValue(d)}));
  rows.sort((a,b)=>{
    let av=a[state.sortKey], bv=b[state.sortKey];
    const numericNullKeys = ["hours","nights","lastModified"];
    if(av==null) av = numericNullKeys.includes(state.sortKey) ? -1 : "";
    if(bv==null) bv = numericNullKeys.includes(state.sortKey) ? -1 : "";
    if(typeof av==="string") return av.localeCompare(bv)*state.sortDir;
    return (av-bv)*state.sortDir;
  });

  document.getElementById("rows").innerHTML = rows.map(d=>{
    const meta = STATUS_META[d.status];
    const img = d.thumb ? `<img class="thumb" src="${d.thumb}" alt="">` : `<div class="thumb-ph">&#9729;</div>`;
    const nameHtml = d.path
      ? `<span class="obj-link" title="Klick öffnet den Ordner">${d.name}</span>`
      : `<span class="obj">${d.name}</span>`;
    return `<tr${d.path?` class="row-link" data-path="${encodeURIComponent(d.path)}"`:""}>
      <td class="img-col"${d.path?` title="Klick wählt das Vorschaubild"`:""}>${img}</td>
      <td>${nameHtml}${d.group?`<span class="obj-sub">Gruppe: ${d.group}</span>`:""}${d.tag?`<span class="obj-sub">Monatshinweis: ${d.tag}</span>`:""}${d.note?`<span class="merge-note">${d.note}</span>`:""}</td>
      <td class="ctr-col"><span class="cat">${d.category}</span></td>
      <td class="ctr-col"><span class="pill ${meta.cls}"><span class="dot"></span>${meta.label}</span></td>
      <td class="num-col">${fmtLastModified(d)}</td>
      <td class="num-col">${d.nights? d.nights : '<span class="none">&ndash;</span>'}</td>
      <td class="num-col">${fmtHours(d)}</td>
      <td class="filters-txt">${d.filters||'<span class="none">&ndash;</span>'}</td>
      <td class="filters-txt">${d.cameras||'<span class="none">&ndash;</span>'}</td>
      <td>${fmtObsCell(d)}</td>
    </tr>`;
  }).join("");
  document.getElementById("countNote").textContent = `${rows.length} von ${DATA.length} Projekten angezeigt`;

  const now = new Date().getMonth()+1;
  const panel = document.getElementById("nowPanel");
  // Das Panel bietet einen Monats-Umschalter (12 Monate durchklickbar,
  // siehe monthChips weiter unten) - deshalb hier ueber ALLE Projekte mit
  // einem Beobachtungsfenster pruefen, nicht nur ueber den aktuellen Monat,
  // damit das Panel auch dann sichtbar bleibt/bedienbar ist, wenn gerade
  // fuer den aktuellen Monat zufaellig nichts Passendes dabei ist.
  const anyObs = DATA.some(d=>d.obs);
  if(anyObs){
    panel.style.display = "";
    const activeForMonth = DATA.filter(d=>d.obs && inWindow(state.previewMonth, d.obs.winStart, d.obs.winEnd) && (!state.hideFinishedNow || d.status!=="done")).sort((a,b)=>b.obs.alt-a.obs.alt);
    document.getElementById("monthChips").innerHTML = MONTHS_DE.map((m,i)=>{
      const monthNum = i+1;
      const cls = ["chip"];
      if(state.previewMonth===monthNum) cls.push("active");
      if(monthNum===now) cls.push("now");
      return `<span class="${cls.join(' ')}" data-month="${monthNum}" title="${monthNum===now?'Aktueller Monat':''}">${m}</span>`;
    }).join("");
    const headLabel = state.previewMonth===now ? `Jetzt (${MONTHS_DE[now-1]})` : MONTHS_DE[state.previewMonth-1];
    document.getElementById("nowHeadText").textContent = `${headLabel} gut zu erreichen – ${activeForMonth.length} Objekte`;
    document.getElementById("nowBody").innerHTML = activeForMonth.length ? activeForMonth.map(d=>
      `<span class="now-card${d.path?' jump':''}"${d.path?` data-path="${encodeURIComponent(d.path)}"`:""} title="${d.path?'Klick springt zur Tabellenzeile':''}"><b>${d.name}</b> <span class="num">${d.obs.alt}°</span>, Höhepunkt ${d.obs.peak}</span>`
    ).join("") : '<span class="none">Für diesen Monat sind keine Objekte gut zu erreichen.</span>';
  } else { panel.style.display = "none"; }

  // Kameranutzung ueber alle Projekte aggregieren
  const camTotals = {};
  DATA.forEach(d=>{
    Object.entries(d.camStats||{}).forEach(([label,v])=>{
      const e = camTotals[label] || (camTotals[label] = {count:0, seconds:0, projects:0});
      e.count += v.count; e.seconds += v.seconds; e.projects += 1;
    });
  });
  const camList = Object.entries(camTotals).sort((a,b)=>b[1].count-a[1].count);
  const camBody = document.getElementById("camBody");
  if(camList.length){
    const maxCount = camList[0][1].count;
    camBody.innerHTML = camList.map(([label,v],i)=>
      `<span class="now-card"><b>${label}</b> <span class="num">${v.count}</span> Aufnahmen &middot; ${(v.seconds/3600).toFixed(1)}h &middot; ${v.projects} Projekte${i===0?' &middot; <b>meistgenutzt</b>':''}</span>`
    ).join("");
  } else {
    camBody.innerHTML = '<span class="none">Keine auswertbaren Dateinamen gefunden.</span>';
  }
}
// scrollIntoView({behavior:"smooth"}) scrollt in manchen WebView2-
// Konfigurationen ueberhaupt nicht (offenbar sobald "smooth" involviert
// ist, bleibt scrollY unveraendert bei 0 - beobachtet und nachgestellt,
// das war der Grund fuer "springt irgendwohin, aber nicht zum Objekt").
// window.scrollTo() mit behavior:"instant" funktioniert zuverlaessig,
// deshalb hier von Hand statt ueber Element.scrollIntoView().
function scrollElementIntoView(el, align){
  const rect = el.getBoundingClientRect();
  const target = align === "center"
    ? rect.top + window.scrollY - (window.innerHeight - rect.height) / 2
    : rect.top + window.scrollY - 12; // "start": kleiner Abstand zum oberen Rand
  window.scrollTo({top: Math.max(0, target), behavior: "instant"});
}
document.getElementById("statusChips").addEventListener("click", e=>{ const el=e.target.closest("[data-status]"); if(!el) return; state.status=el.dataset.status; render(); });
// Statistik-Kacheln oben (Projekte gesamt/Fertig/In Arbeit/Geplant/Status
// unklar) filtern beim Anklicken direkt die Tabelle auf denselben Status,
// analog zu den Status-Chips im Filterbereich, und scrollen die Tabelle
// in den sichtbaren Bereich, damit die gefilterte Liste sofort sichtbar
// wird.
document.getElementById("stats").addEventListener("click", e=>{
  const el = e.target.closest("[data-stat-status]");
  if(!el) return;
  state.status = el.dataset.statStatus;
  render();
  scrollElementIntoView(document.querySelector(".tablewrap"), "start");
});
document.getElementById("catChips").addEventListener("click", e=>{ const el=e.target.closest("[data-cat]"); if(!el) return; state.cat=el.dataset.cat; render(); });
document.getElementById("monthChips").addEventListener("click", e=>{ const el=e.target.closest("[data-month]"); if(!el) return; state.previewMonth=parseInt(el.dataset.month,10); render(); });
document.getElementById("hideFinishedNow").addEventListener("change", e=>{ state.hideFinishedNow=e.target.checked; render(); });
// Objekt-Karten im "Jetzt gut zu erreichen"-Panel springen zur passenden
// Tabellenzeile: Filter werden dafuer zurueckgesetzt (sonst waere die
// Zeile eventuell gar nicht sichtbar), dann wird die Zeile in den
// sichtbaren Bereich gescrollt und kurz farblich hervorgehoben.
document.getElementById("nowBody").addEventListener("click", e=>{
  const el = e.target.closest(".now-card.jump[data-path]");
  if(!el) return;
  state.status = "all"; state.cat = "all"; state.q = "";
  document.getElementById("searchBox").value = "";
  render();
  const row = document.querySelector(`tbody tr[data-path="${el.dataset.path}"]`);
  if(!row) return;
  scrollElementIntoView(row, "center");
  row.classList.remove("row-flash");
  void row.offsetWidth; // Reflow erzwingen, damit die Animation bei erneutem Klick neu startet
  row.classList.add("row-flash");
  row.addEventListener("animationend", ()=> row.classList.remove("row-flash"), {once:true});
});
document.getElementById("searchBox").addEventListener("input", e=>{ state.q=e.target.value.trim().toLowerCase(); render(); });
document.querySelectorAll("thead th[data-key]").forEach(th=>{ th.addEventListener("click", ()=>{ const key=th.dataset.key; if(state.sortKey===key){state.sortDir*=-1;}else{state.sortKey=key;state.sortDir=1;} render(); }); });
// Klick auf eine Zeile oeffnet den Ordner (siehe openFolder() oben), Klick
// auf das Vorschaubild oeffnet stattdessen die Bildauswahl (siehe
// openPreviewPicker() weiter unten) - beides ueber denselben Tabellenkoerper
// delegiert, damit ein einziger Listener auch fuer neu gerenderte Zeilen
// funktioniert. Die Bildzelle wird zuerst geprueft und beendet den Handler
// dann mit return, damit nicht zusaetzlich noch der Ordner geoeffnet wird.
document.getElementById("rows").addEventListener("click", e=>{
  const thumbCell = e.target.closest("td.img-col");
  if(thumbCell){
    const tr = thumbCell.closest("tr[data-path]");
    if(tr) openPreviewPicker(decodeURIComponent(tr.dataset.path));
    return;
  }
  const tr = e.target.closest("tr[data-path]");
  if(!tr) return;
  const path = decodeURIComponent(tr.dataset.path);
  openFolder(path);
});

// ----------------------------------------------------------------------
// Vorschaubild-Auswahlfenster (Klick auf das Vorschaubild in der Tabelle)
// ----------------------------------------------------------------------
const previewPickerOverlay = document.getElementById("previewPickerOverlay");
const previewPickerHint = document.getElementById("previewPickerHint");
const previewPickerGrid = document.getElementById("previewPickerGrid");
let previewPickerPath = null;

function closePreviewPicker(){ previewPickerOverlay.hidden = true; previewPickerPath = null; }

function openPreviewPicker(path){
  previewPickerPath = path;
  previewPickerHint.textContent = "Lade Bilder …";
  previewPickerGrid.innerHTML = "";
  previewPickerOverlay.hidden = false;
  window.pywebview.api.list_preview_candidates(path).then(result=>{
    if(previewPickerPath !== path) return; // Fenster wurde inzwischen fuer ein anderes Projekt geoeffnet
    if(!result.ok){
      previewPickerHint.textContent = result.error || "Fehler beim Laden.";
      return;
    }
    previewPickerHint.textContent = result.items.length
      ? "Klick auf ein Bild übernimmt es sofort als Vorschau."
      : "Keine Bilddateien in diesem Ordner gefunden.";
    const cur = result.current;
    const tiles = [];
    tiles.push(`<div class="preview-picker-item${cur.mode==="auto"?" active":""}" data-mode="auto">`
      + `<div class="ph">&#9733;</div><div class="lbl">Automatisch</div></div>`);
    tiles.push(`<div class="preview-picker-item${cur.mode==="none"?" active":""}" data-mode="none">`
      + `<div class="ph">&#8709;</div><div class="lbl">Kein Bild</div></div>`);
    for(const it of result.items){
      const active = cur.mode==="file" && cur.path===it.path;
      const inner = it.thumb ? `<img src="${it.thumb}" alt="">` : `<div class="ph">&#9729;</div>`;
      tiles.push(`<div class="preview-picker-item${active?" active":""}" data-mode="file" `
        + `data-relpath="${encodeURIComponent(it.path)}">${inner}<div class="lbl">${it.name}</div></div>`);
    }
    previewPickerGrid.innerHTML = tiles.join("");
  }).catch(err=>{
    previewPickerHint.textContent = "Fehler: " + err;
  });
}

document.getElementById("closePreviewPickerBtn").addEventListener("click", closePreviewPicker);
previewPickerOverlay.addEventListener("click", e=>{ if(e.target===previewPickerOverlay) closePreviewPicker(); });

previewPickerGrid.addEventListener("click", e=>{
  const tile = e.target.closest(".preview-picker-item");
  if(!tile || !previewPickerPath) return;
  const mode = tile.dataset.mode;
  const relPath = mode==="file" ? decodeURIComponent(tile.dataset.relpath) : null;
  previewPickerHint.textContent = "Wird gespeichert …";
  window.pywebview.api.set_preview_override(previewPickerPath, mode, relPath).then(result=>{
    if(result.ok){
      closePreviewPicker();
      location.reload();
    } else {
      previewPickerHint.textContent = result.error || "Fehler beim Speichern.";
    }
  }).catch(err=>{
    previewPickerHint.textContent = "Fehler: " + err;
  });
});

render();

// ----------------------------------------------------------------------
// Einstellungen (Zahnrad). Funktioniert nur in der App-Ansicht (pywebview),
// da nur dort window.pywebview.api.* zur Verfuegung steht; im Browser-
// Fallback (pywebview fehlt) zeigt der Knopf stattdessen einen Hinweis,
// dass die Einstellungen dann per Texteditor (AstroLogbuch_config.json)
// bearbeitet werden muessen.
let hasWebviewApi = !!(window.pywebview && window.pywebview.api);
window.addEventListener("pywebviewready", ()=>{ hasWebviewApi = true; });

function mapToRows(container, mapObj, keyPh, valPh){
  container.innerHTML = "";
  const entries = Object.entries(mapObj || {});
  if(entries.length===0) entries.push(["", ""]);
  entries.forEach(([k,v])=> addMapRow(container, k, v, keyPh, valPh));
}
function addMapRow(container, k, v, keyPh, valPh){
  const row = document.createElement("div");
  row.className = "map-row";
  row.innerHTML = `<input type="text" class="map-key" placeholder="${keyPh}" value="${k?String(k).replace(/"/g,'&quot;'):''}">`
    + `<input type="text" class="map-val" placeholder="${valPh}" value="${v?String(v).replace(/"/g,'&quot;'):''}">`
    + `<button class="btn tiny" type="button">&times;</button>`;
  row.querySelector("button").addEventListener("click", ()=> row.remove());
  container.appendChild(row);
}
function rowsToMap(container){
  const out = {};
  container.querySelectorAll(".map-row").forEach(row=>{
    const k = row.querySelector(".map-key").value.trim();
    const v = row.querySelector(".map-val").value.trim();
    if(k) out[k] = v;
  });
  return out;
}

const settingsOverlay = document.getElementById("settingsOverlay");
const settingsStatus = document.getElementById("settingsStatus");
const cameraMapTable = document.getElementById("cameraMapTable");
const filterMapTable = document.getElementById("filterMapTable");

function openSettings(){
  settingsStatus.textContent = "";
  settingsStatus.className = "settings-status";
  document.getElementById("cfgPlaceName").value = "";
  const placeStatus = document.getElementById("placeLookupStatus");
  placeStatus.textContent = "";
  placeStatus.style.color = "";
  const fallbackNote = document.getElementById("settingsFallbackNote");
  const form = document.getElementById("settingsForm");
  if(!hasWebviewApi){
    fallbackNote.hidden = false;
    form.style.display = "none";
    document.getElementById("saveSettingsBtn").hidden = true;
    settingsOverlay.hidden = false;
    return;
  }
  fallbackNote.hidden = true;
  form.style.display = "";
  document.getElementById("saveSettingsBtn").hidden = false;
  window.pywebview.api.get_config().then(cfg=>{
    document.getElementById("cfgRootFolder").value = cfg.root_folder || "";
    document.getElementById("cfgLatitude").value = cfg.latitude;
    document.getElementById("cfgOnlineLookup").checked = !!cfg.online_lookup_enabled;
    document.getElementById("cfgShowThumbnails").checked = !!cfg.show_thumbnails;
    document.getElementById("cfgExcludeFolders").value = (cfg.exclude_folder_names || []).join(", ");
    document.getElementById("cfgCalibWords").value = (cfg.calib_words || []).join(", ");
    mapToRows(cameraMapTable, cfg.camera_map, "Rohcode, z. B. 2600", "Anzeigename, z. B. ASI2600");
    mapToRows(filterMapTable, cfg.filter_map, "Kürzel, z. B. H", "Anzeigename, z. B. Ha");
    settingsOverlay.hidden = false;
  }).catch(err=>{
    settingsStatus.textContent = "Konnte Einstellungen nicht laden: " + err;
    settingsStatus.className = "settings-status err";
    settingsOverlay.hidden = false;
  });
}
function closeSettings(){ settingsOverlay.hidden = true; }

document.getElementById("settingsBtn").addEventListener("click", openSettings);
document.getElementById("cancelSettingsBtn").addEventListener("click", closeSettings);
settingsOverlay.addEventListener("click", e=>{ if(e.target===settingsOverlay) closeSettings(); });

document.getElementById("pickFolderBtn").addEventListener("click", ()=>{
  if(!hasWebviewApi) return;
  window.pywebview.api.pick_folder().then(res=>{
    if(res && res.path) document.getElementById("cfgRootFolder").value = res.path;
  });
});
document.getElementById("lookupPlaceBtn").addEventListener("click", ()=>{
  const statusEl = document.getElementById("placeLookupStatus");
  if(!hasWebviewApi){
    statusEl.textContent = "Ortssuche geht nur in der App-Ansicht (nicht im Browser-Fallback).";
    statusEl.style.color = "var(--bad)";
    return;
  }
  const place = document.getElementById("cfgPlaceName").value.trim();
  if(!place){
    statusEl.textContent = "Bitte zuerst einen Ort eingeben.";
    statusEl.style.color = "var(--bad)";
    return;
  }
  statusEl.textContent = "Suche ...";
  statusEl.style.color = "";
  window.pywebview.api.resolve_place_latitude(place).then(res=>{
    if(res && res.ok){
      document.getElementById("cfgLatitude").value = res.latitude;
      statusEl.textContent = `Gefunden: ${res.displayName} → ${res.latitude}° (Breitengrad oben eingetragen, bitte pruefen und dann speichern)`;
      statusEl.style.color = "var(--good)";
    } else {
      statusEl.textContent = (res && res.error) || "Unbekannter Fehler bei der Ortssuche.";
      statusEl.style.color = "var(--bad)";
    }
  }).catch(err=>{
    statusEl.textContent = "Fehler: " + err;
    statusEl.style.color = "var(--bad)";
  });
});
document.getElementById("addCameraRowBtn").addEventListener("click", ()=> addMapRow(cameraMapTable, "", "", "Rohcode, z. B. 2600", "Anzeigename, z. B. ASI2600"));
document.getElementById("addFilterRowBtn").addEventListener("click", ()=> addMapRow(filterMapTable, "", "", "Kürzel, z. B. H", "Anzeigename, z. B. Ha"));

document.getElementById("saveSettingsBtn").addEventListener("click", ()=>{
  const splitList = s => s.split(",").map(x=>x.trim()).filter(Boolean);
  const cfg = {
    root_folder: document.getElementById("cfgRootFolder").value.trim(),
    latitude: parseFloat(document.getElementById("cfgLatitude").value),
    online_lookup_enabled: document.getElementById("cfgOnlineLookup").checked,
    show_thumbnails: document.getElementById("cfgShowThumbnails").checked,
    exclude_folder_names: splitList(document.getElementById("cfgExcludeFolders").value),
    calib_words: splitList(document.getElementById("cfgCalibWords").value),
    camera_map: rowsToMap(cameraMapTable),
    filter_map: rowsToMap(filterMapTable),
  };
  if(!cfg.root_folder){
    settingsStatus.textContent = "Bitte zuerst einen Ordner wählen.";
    settingsStatus.className = "settings-status err";
    return;
  }
  if(Number.isNaN(cfg.latitude)){
    settingsStatus.textContent = "Bitte einen gültigen Breitengrad eingeben.";
    settingsStatus.className = "settings-status err";
    return;
  }
  settingsStatus.textContent = "Wird gespeichert und neu eingelesen …";
  settingsStatus.className = "settings-status";
  window.pywebview.api.apply_settings(cfg).then(result=>{
    if(result.ok){
      settingsStatus.textContent = `Gespeichert, ${result.count} Projekte gefunden. Lade neu …`;
      settingsStatus.className = "settings-status ok";
      setTimeout(()=> location.reload(), 600);
    } else {
      settingsStatus.textContent = result.error || "Unbekannter Fehler.";
      settingsStatus.className = "settings-status err";
    }
  }).catch(err=>{
    settingsStatus.textContent = "Fehler: " + err;
    settingsStatus.className = "settings-status err";
  });
});
</script>
</body>
</html>
"""


def build_dashboard_html(projects, root_folder):
    from datetime import datetime
    out = HTML_TEMPLATE
    out = out.replace("%%ROOT_FOLDER%%", html.escape(root_folder))
    out = out.replace("%%HEADER_LOGO_B64%%", HEADER_LOGO_PNG_BASE64)
    out = out.replace("%%TIMESTAMP%%", datetime.now().strftime("%d.%m.%Y %H:%M"))
    out = out.replace("%%LATITUDE%%", str(LATITUDE))
    out = out.replace("%%APP_VERSION%%", APP_VERSION)
    out = out.replace("%%DATA_JSON%%", json.dumps(projects, ensure_ascii=False))
    return out


# ======================================================================
# Lokaler Mini-Server
# ======================================================================
# Ein im Browser aus Sicherheitsgruenden unmoeglicher "oeffne diesen Ordner
# im Explorer"-Klick lässt sich nur ueber ein Programm loesen, das dafuer
# tatsaechlich lokal auf dem Rechner laeuft. Deshalb wird das Dashboard,
# solange dieses Skript/die .exe laeuft, ueber eine lokale Adresse
# (http://127.0.0.1:<port>/) bedient statt nur als Datei geschrieben; ein
# Klick auf eine Zeile fragt dort per fetch("/open?path=...") an, und
# open_in_explorer() unten oeffnet den Ordner dann direkt mit den Mitteln
# des jeweiligen Betriebssystems. Die Datei AstroLogbuch.html wird
# zusaetzlich weiterhin geschrieben (z. B. um sie spaeter erneut
# anzuschauen); ohne laufendes Programm kopiert ein Klick darin dann nur
# noch den Pfad in die Zwischenablage (siehe openFolder() im JS-Teil oben).

def open_in_explorer(path):
    if sys.platform == "win32":
        os.startfile(path)  # type: ignore[attr-defined]
    elif sys.platform == "darwin":
        subprocess.Popen(["open", path])
    else:
        subprocess.Popen(["xdg-open", path])


def make_dashboard_handler(state):
    """state ist ein gemeinsam genutztes Dict mit den Schluesseln
    "html_bytes" und "root_folder". Beide koennen sich waehrend der
    Laufzeit aendern (z. B. nach einem Ordnerwechsel/Rescan in den
    Einstellungen), der Handler liest sie deshalb bei jeder Anfrage frisch
    aus state, statt sie sich beim Start einmalig zu merken."""

    class DashboardHandler(http.server.BaseHTTPRequestHandler):
        def log_message(self, fmt, *args):
            pass  # keine Konsolen-Zeile pro Klick/Request

        def do_GET(self):
            parsed = urlparse(self.path)
            if parsed.path in ("/", "/index.html", "/AstroLogbuch.html"):
                html_bytes = state["html_bytes"]
                self.send_response(200)
                self.send_header("Content-Type", "text/html; charset=utf-8")
                self.send_header("Content-Length", str(len(html_bytes)))
                self.end_headers()
                self.wfile.write(html_bytes)
                return
            if parsed.path == "/progress":
                # Wird vom Splash-Screen (render_loading_page) alle paar
                # 100ms abgefragt, solange das Fenster noch die Ladeseite
                # zeigt. Ausserhalb des allerersten Starts (also z. B. im
                # fertigen Dashboard) fragt niemand diese Route ab, daher
                # reicht ein simpler Default ohne Bedeutung.
                progress = state.get("progress") or {"current": 0, "total": 0, "text": "", "log": []}
                body = json.dumps(progress).encode("utf-8")
                self.send_response(200)
                self.send_header("Content-Type", "application/json; charset=utf-8")
                self.send_header("Content-Length", str(len(body)))
                self.send_header("Cache-Control", "no-store")
                self.end_headers()
                self.wfile.write(body)
                return
            if parsed.path == "/open":
                target = parse_qs(parsed.query).get("path", [""])[0]
                ok = False
                try:
                    root_folder = state.get("root_folder") or ""
                    norm_root = os.path.normcase(os.path.normpath(os.path.abspath(root_folder)))
                    norm_target = os.path.normcase(os.path.normpath(os.path.abspath(target)))
                    # Sicherheitshalber nur Ordner innerhalb von ROOT_FOLDER
                    # oeffnen, nie einen beliebigen vom Browser mitgegebenen Pfad.
                    # os.path.commonpath() statt eines manuellen
                    # startswith(root + os.sep)-Vergleichs: Ist der
                    # Astro-Ordner eine reine Laufwerkswurzel (z. B. "K:\"),
                    # behaelt os.path.normpath() dort bewusst den
                    # abschliessenden Backslash (das ist unter Windows die
                    # einzig gueltige Schreibweise fuer eine Laufwerkswurzel),
                    # wodurch "root + os.sep" faelschlich einen doppelten
                    # Backslash ergab und dadurch JEDE Unterordner-Pruefung
                    # scheitern liess - beobachtet als "Kann Ordner nicht
                    # oeffnen" bei allen Projekten, sobald der Astro-Ordner
                    # direkt eine Laufwerkswurzel war. commonpath() vergleicht
                    # stattdessen ueber die einzelnen Pfadbestandteile und ist
                    # von diesem Sonderfall nicht betroffen.
                    try:
                        inside_root = os.path.commonpath([norm_root, norm_target]) == norm_root
                    except ValueError:
                        inside_root = False  # z. B. unterschiedliche Laufwerke
                    if inside_root and os.path.isdir(target):
                        open_in_explorer(target)
                        ok = True
                except Exception:
                    ok = False
                self.send_response(204 if ok else 400)
                self.end_headers()
                return
            self.send_response(404)
            self.end_headers()

    return DashboardHandler


def render_status_page(message, spinner=False, detail=""):
    """Sehr einfache, abhaengigkeitsfreie Platzhalter-/Fehlerseite (Laden,
    kein Ordner gewaehlt, Absturz beim Rescan). Bewusst kein Google-Fonts-
    Link wie im eigentlichen Dashboard, damit sie auch ohne Internet und
    ohne einen fertigen Scan sofort anzeigbar ist."""
    spin_css = """
    .spin{width:34px;height:34px;border-radius:50%;border:3px solid #dbd6c6;
      border-top-color:#a85a2b;animation:spin 0.9s linear infinite;margin:0 auto 18px;}
    @keyframes spin{to{transform:rotate(360deg);}}
    """ if spinner else ""
    spin_html = '<div class="spin"></div>' if spinner else ""
    detail_html = f'<pre>{html.escape(detail)}</pre>' if detail else ""
    return f"""<!doctype html><html lang="de"><head><meta charset="utf-8">
<title>AstroLogbuch</title>
<style>
  body{{margin:0;min-height:100vh;display:flex;align-items:center;justify-content:center;
    background:#f6f4ee;color:#20241f;font:15px/1.5 -apple-system,Segoe UI,sans-serif;}}
  .box{{max-width:520px;text-align:center;padding:32px;}}
  h1{{font-size:17px;margin:0 0 8px;}}
  p{{color:#5c6156;margin:0;}}
  pre{{text-align:left;background:#eeece2;border:1px solid #dbd6c6;border-radius:8px;
    padding:12px;margin-top:16px;font-size:12px;overflow:auto;max-height:220px;white-space:pre-wrap;}}
  {spin_css}
</style></head><body>
<div class="box">{spin_html}<h1>{html.escape(message)}</h1>{detail_html}</div>
</body></html>"""


# Splash-Screen fuer den allerersten Scan beim Programmstart (siehe
# try_launch_webview/on_start). Pollt /progress, das waehrend scan_root()
# ueber progress_cb aktualisiert wird, und zeigt so Fortschrittsbalken und
# Lesestatus wie im Konsolenfenster an. %%LOGO_B64%% wird per einfachem
# Text-Ersetzen eingesetzt (kein f-string, spart das Verdoppeln jeder
# CSS-/JS-geschweiften Klammer).
LOADING_HTML_TEMPLATE = r"""<!doctype html><html lang="de"><head><meta charset="utf-8">
<title>AstroLogbuch</title>
<style>
  body{margin:0;min-height:100vh;display:flex;flex-direction:column;align-items:center;justify-content:center;
    background:#0d1119;color:#e9ecf3;font:14px/1.5 -apple-system,Segoe UI,sans-serif;}
  .logo{width:240px;height:240px;margin-bottom:32px;border-radius:46px;filter:drop-shadow(0 10px 28px rgba(0,0,0,.45));}
  .bar-track{width:380px;max-width:80vw;height:6px;border-radius:3px;background:#212a3a;overflow:hidden;margin-bottom:12px;}
  .bar-fill{height:100%;width:2%;background:#e4a15c;border-radius:3px;transition:width .25s ease;}
  .status{font-size:12.5px;color:#a3acc2;min-height:16px;margin-bottom:18px;text-align:center;max-width:80vw;}
  .log{width:480px;max-width:86vw;height:160px;overflow-y:auto;background:#151b28;border:1px solid #2b3548;
    border-radius:8px;padding:10px 12px;font:12px/1.6 'IBM Plex Mono',ui-monospace,Consolas,monospace;color:#6f7996;}
  .log div{white-space:nowrap;overflow:hidden;text-overflow:ellipsis;}
  .log div:last-child{color:#e9ecf3;}
</style></head><body>
<img class="logo" src="data:image/png;base64,%%LOGO_B64%%" alt="AstroLogbuch">
<div class="bar-track"><div class="bar-fill" id="barFill"></div></div>
<div class="status" id="statusText">Initialisiere ...</div>
<div class="log" id="logBox"></div>
<script>
function esc(s){ return s.replace(/&/g,"&amp;").replace(/</g,"&lt;"); }
async function poll(){
  try{
    const r = await fetch("/progress", {cache:"no-store"});
    const p = await r.json();
    const pct = p.total > 0 ? Math.min(100, Math.round(p.current / p.total * 100)) : 100;
    document.getElementById("barFill").style.width = Math.max(2, pct) + "%";
    document.getElementById("statusText").textContent = p.text || "";
    const logBox = document.getElementById("logBox");
    logBox.innerHTML = (p.log || []).map(l => "<div>" + esc(l) + "</div>").join("");
    logBox.scrollTop = logBox.scrollHeight;
  }catch(e){ /* Server kurz nicht erreichbar, naechster Poll versucht's erneut */ }
}
poll();
setInterval(poll, 350);
</script>
</body></html>"""


def render_loading_page():
    return LOADING_HTML_TEMPLATE.replace("%%LOGO_B64%%", APP_LOGO_PNG_BASE64)


def run_scan_and_build(out_dir, thumb_cache_path, object_cache_path, progress_cb=None):
    """Fuehrt einen kompletten Scan mit den aktuell gueltigen (globalen)
    Einstellungen durch, schreibt AstroLogbuch.html und gibt den fertigen
    HTML-Inhalt plus Projektanzahl zurueck. Wirft eine Exception weiter,
    wenn der Ordner nicht existiert o.ae. - die Aufrufer entscheiden, wie
    das jeweils angezeigt wird (Konsole bzw. Fehlerseite im Programmfenster).

    progress_cb(current, total, text) wird optional bei jedem Scan-Schritt
    aufgerufen, siehe scan_root(). Fuer den Splash-Screen (render_loading_page)
    genuegen zusaetzliche Aufrufe ohne current/total (nur text), um eine
    Statuszeile zu setzen, ohne den Fortschrittsbalken zu veraendern."""
    if not ROOT_FOLDER or not os.path.isdir(ROOT_FOLDER):
        raise FileNotFoundError(f"Ordner nicht gefunden: {ROOT_FOLDER}")

    start = time.time()
    print(f"Scanne: {ROOT_FOLDER}", flush=True)
    if progress_cb:
        progress_cb(text=f"Scanne: {ROOT_FOLDER}")
    ref_year = date.today().year
    projects = scan_root(ROOT_FOLDER, ref_year, thumb_cache_path=thumb_cache_path,
                          object_cache_path=object_cache_path, progress_cb=progress_cb)
    elapsed = time.time() - start
    done_line = f"{len(projects)} Projektordner gefunden ({elapsed:.1f} Sekunden)."
    print(done_line, flush=True)
    if progress_cb:
        progress_cb(text=done_line)

    html_content = build_dashboard_html(projects, ROOT_FOLDER)
    output_html = os.path.join(out_dir, "AstroLogbuch.html")
    try:
        with open(output_html, "w", encoding="utf-8") as f:
            f.write(html_content)
        print(f"Dashboard geschrieben: {output_html}", flush=True)
    except Exception:
        pass  # das Anzeigen im Programmfenster funktioniert auch ohne diese Datei
    return html_content, len(projects)


# ======================================================================
# App-Fenster (pywebview) - Standardweg ohne Browser
# ======================================================================
# Zeigt das bestehende HTML/CSS/JS-Dashboard unveraendert in einem eigenen
# Programmfenster an (kein Browser-Tab, keine Adressleiste), ueber die
# kleine Zusatzbibliothek "pywebview" (pip install pywebview). Ist sie
# nicht installiert oder schlaegt das Erstellen des Fensters aus
# irgendeinem Grund fehl, faellt das Programm automatisch auf den
# klassischen Browser-Modus zurueck (siehe run_legacy_browser_mode()),
# statt einfach abzustuerzen.

def pick_folder_dialog(window, initial_dir=""):
    """Oeffnet den nativen Ordnerauswahl-Dialog und gibt den gewaehlten Pfad
    zurueck (oder None bei Abbruch). Kapselt die kleinen Unterschiede
    zwischen pywebview-Versionen (Rueckgabe als Tupel oder als reiner
    String)."""
    import webview
    try:
        result = window.create_file_dialog(webview.FileDialog.FOLDER, directory=initial_dir or "")
    except Exception:
        return None
    if not result:
        return None
    if isinstance(result, (list, tuple)):
        return result[0] if result else None
    return str(result)


class Api:
    """Wird pywebview als js_api uebergeben; jede oeffentliche Methode ist
    danach im Dashboard aus JavaScript ueber window.pywebview.api.<name>(...)
    aufrufbar (liefert ein Promise). self._window wird erst nach dem
    Erstellen des Fensters gesetzt (siehe try_launch_webview()).

    WICHTIG: Das Fenster-Objekt bewusst als self._window (mit Unterstrich)
    ablegen, nicht self.window. pywebview baut die JS-API-Bruecke bei JEDER
    Navigation (also auch bei jedem reload_window()) ueber get_functions()
    in webview/util.py neu auf, das dabei rekursiv ALLE oeffentlichen
    (nicht mit "_" beginnenden) Attribute dieses Api-Objekts durchwandert.
    Waere hier ein self.window mit dem echten Fenster-Objekt hinterlegt,
    wuerde dieser Durchlauf auch in window.native (das rohe .NET/WinForms-
    Objekt) hineinlaufen und sich dort in einer Endlosrekursion verheddern
    (z. B. Rectangle.Empty.Empty.Empty...), weil jeder pythonnet-Zugriff
    ein neues Wrapper-Objekt mit neuer id() erzeugt und die
    Schon-besucht-Erkennung von get_functions() das daher nicht abfangen
    kann. Beobachtet als: Programmfenster friert nach dem Laden bei
    normaler Benutzung immer wieder ein ("Keine Rueckmeldung"), begleitet
    von wiederholten "[pywebview] Error while processing
    window.native.AccessibilityObject...maximum recursion depth exceeded"
    im Log. Mit dem Unterstrich ueberspringt get_functions() dieses
    Attribut von vornherein (siehe "if name.startswith('_'): continue")."""

    def __init__(self, state, config_path, thumb_cache_path, object_cache_path, out_dir):
        self.state = state
        self.config_path = config_path
        self.thumb_cache_path = thumb_cache_path
        self.object_cache_path = object_cache_path
        self.out_dir = out_dir
        self._window = None

    def pick_folder(self):
        path = pick_folder_dialog(self._window, ROOT_FOLDER)
        return {"path": path}

    def get_config(self):
        return load_config(self.config_path)

    def resolve_place_latitude(self, place_name):
        """Wird vom "Koordinate suchen"-Knopf im Einstellungen-Panel
        aufgerufen (siehe resolve_place_latitude() oben fuer die eigentliche
        Nominatim-Abfrage)."""
        return resolve_place_latitude(place_name)

    def apply_settings(self, new_cfg, progress_cb=None):
        """Speichert eine vollstaendige neue Konfiguration und liest den
        (moeglicherweise geaenderten) Ordner sofort neu ein. Wird sowohl
        vom "Speichern"-Knopf der Einstellungen als auch beim allerersten
        Start (nach der Ordnerauswahl) verwendet.

        progress_cb wird nur beim allerersten Start (aus on_start()) mitgegeben,
        damit der Splash-Screen live mitzaehlt; von JS aus (Einstellungen-Panel,
        Knopf "Speichern & neu einlesen") wird apply_settings() ohne dieses
        Argument aufgerufen, dort bleibt der Fortschritt daher unsichtbar.

        Basis ist bewusst die ZULETZT GESPEICHERTE Config (load_config), nicht
        die blanke Werksvorgabe: new_cfg vom Einstellungen-Panel enthaelt nur
        die dortigen Formularfelder, nicht z. B. preview_overrides (siehe
        set_preview_override() weiter unten). Mit DEFAULT_CONFIG als Basis
        wuerde ein ganz normales "Speichern & neu einlesen" alle bisher per
        Vorschaubild-Auswahl gesetzten Overrides stillschweigend auf {}
        zuruecksetzen."""
        cfg = load_config(self.config_path)
        if isinstance(new_cfg, dict):
            cfg.update(new_cfg)

        root = str(cfg.get("root_folder") or "").strip()
        if not root or not os.path.isdir(root):
            return {"ok": False, "error": f"Ordner nicht gefunden: {root}"}
        try:
            cfg["latitude"] = float(cfg.get("latitude", DEFAULT_CONFIG["latitude"]))
        except (TypeError, ValueError):
            return {"ok": False, "error": "Ungültiger Breitengrad (bitte eine Zahl, z. B. 47.65)."}

        save_config(self.config_path, cfg)
        apply_config(cfg)
        try:
            html_content, count = run_scan_and_build(
                self.out_dir, self.thumb_cache_path, self.object_cache_path, progress_cb=progress_cb)
        except Exception as exc:
            traceback.print_exc()
            return {"ok": False, "error": f"Fehler beim Einlesen des Ordners: {exc}"}

        self.state["html_bytes"] = html_content.encode("utf-8")
        self.state["root_folder"] = ROOT_FOLDER
        return {"ok": True, "count": count}

    def rescan(self):
        """Aktuellen Ordner mit den bestehenden Einstellungen erneut
        einlesen, ohne dass sich an den Einstellungen etwas aendert
        (z. B. ueber einen "Aktualisieren"-Knopf im Dashboard)."""
        return self.apply_settings(load_config(self.config_path))

    def list_preview_candidates(self, project_path):
        """Fuer das Vorschaubild-Auswahlfenster (Klick auf das Vorschaubild
        in der Tabelle): alle infrage kommenden Bilddateien (jpg/png/tif/tiff)
        im gegebenen Projektordner, jeweils mit Mini-Vorschau. Bewusst OHNE
        die Screenshot-Namen-Filterung der automatischen Heuristik
        (pick_preview_file) - hier waehlt der Nutzer selbst bewusst aus, da
        darf z. B. auch eine "...annotated..."-Datei zur Auswahl stehen.
        Nutzt denselben Thumbnail-Cache wie der normale Scan, damit bereits
        erzeugte Vorschaubilder nicht doppelt berechnet werden."""
        if not project_path or not os.path.isdir(project_path):
            return {"ok": False, "error": "Ordner nicht gefunden.", "items": []}
        try:
            scan = scan_project(project_path)
        except Exception as exc:
            traceback.print_exc()
            return {"ok": False, "error": str(exc), "items": []}

        old_cache = load_thumb_cache(self.thumb_cache_path)
        used_cache = {}
        stats = {"hits": 0, "new": 0}
        items = []
        for rel, size, mtime in scan["final_files"]:
            ext = os.path.splitext(rel)[1].lower()
            if ext not in PREVIEW_EXT_SET:
                continue
            full = os.path.join(project_path, rel)
            thumb = get_thumbnail_cached(
                full, size, mtime, old_cache, used_cache, stats,
                max_bytes=PREVIEW_PICKER_MAX_THUMB_BYTES)
            items.append({"path": rel, "name": os.path.basename(rel), "thumb": thumb})
        if used_cache:
            merged = dict(old_cache)
            merged.update(used_cache)
            save_thumb_cache(self.thumb_cache_path, merged)
        items.sort(key=lambda it: it["name"].lower())

        if project_path not in PREVIEW_OVERRIDES:
            current = {"mode": "auto"}
        elif PREVIEW_OVERRIDES[project_path] is None:
            current = {"mode": "none"}
        else:
            current = {"mode": "file", "path": PREVIEW_OVERRIDES[project_path]}
        return {"ok": True, "items": items, "current": current}

    def set_preview_override(self, project_path, mode, rel_path=None):
        """Speichert die manuelle Vorschaubild-Wahl fuer ein Projekt
        dauerhaft (Feld preview_overrides in AstroLogbuch_config.json) und
        liest den Ordner danach neu ein, damit die Aenderung sofort sichtbar
        wird. mode: "auto" (Eintrag entfernen, wieder automatische
        Heuristik), "none" (explizit kein Bild) oder "file" (rel_path als
        Vorschau verwenden)."""
        if not project_path:
            return {"ok": False, "error": "Kein Projektpfad angegeben."}
        cfg = load_config(self.config_path)
        overrides = dict(cfg.get("preview_overrides") or {})
        if mode == "auto":
            overrides.pop(project_path, None)
        elif mode == "none":
            overrides[project_path] = None
        elif mode == "file" and rel_path:
            overrides[project_path] = rel_path
        else:
            return {"ok": False, "error": "Ungültige Auswahl."}
        cfg["preview_overrides"] = overrides
        return self.apply_settings(cfg)


def try_launch_webview(config, config_path, thumb_cache_path, object_cache_path, out_dir):
    """Baut das App-Fenster auf und blockiert (wie server.serve_forever()
    vorher), bis das Fenster geschlossen wird. Gibt True zurueck, wenn das
    grundsaetzlich funktioniert hat (auch wenn z. B. der Scan selbst einen
    Fehler ergab - der wird dann als Seite IM Fenster angezeigt). Gibt
    False zurueck, wenn pywebview fehlt oder das Fenster aus einem anderen
    Grund gar nicht erst aufgebaut werden konnte, damit main() dann auf den
    Browser-Modus zurueckfallen kann."""
    try:
        import webview
    except ImportError:
        print("Hinweis: Paket 'pywebview' nicht gefunden, verwende den Browser-Modus.")
        print("Fuer die App-Ansicht ohne Browser einmalig: pip install pywebview\n", flush=True)
        return False

    state = {"html_bytes": render_loading_page().encode("utf-8"),
             "root_folder": config.get("root_folder") or "",
             "progress": {"current": 0, "total": 0, "text": "Initialisiere ...", "log": []}}
    handler_cls = make_dashboard_handler(state)
    try:
        server = http.server.HTTPServer(("127.0.0.1", 0), handler_cls)
    except OSError:
        traceback.print_exc()
        print("Konnte keinen lokalen Server starten, verwende den Browser-Modus.")
        return False

    port = server.server_address[1]
    url = f"http://127.0.0.1:{port}/"
    threading.Thread(target=server.serve_forever, daemon=True).start()

    api = Api(state, config_path, thumb_cache_path, object_cache_path, out_dir)

    def progress_cb(current=None, total=None, text=None):
        """Aktualisiert state["progress"], das /progress fuer den
        Splash-Screen (render_loading_page) per Polling ausliefert. current/
        total bewusst optional: run_scan_and_build() setzt fuer reine
        Zwischen-Statuszeilen (z. B. "Dashboard wird geschrieben") nur text,
        ohne den zuletzt erreichten Fortschrittsbalken zurueckzusetzen."""
        p = state["progress"]
        if total is not None:
            p["total"] = total
        if current is not None:
            p["current"] = current
        if text:
            p["text"] = text
            log = p["log"]
            log.append(text)
            del log[:-14]  # nur die letzten 14 Zeilen behalten, wie ein kleines Konsolenfenster

    def reload_window():
        # WebView2 (der Windows-Backend von pywebview) behandelt das Setzen
        # von Source auf exakt dieselbe URL als reine No-Op-Zuweisung, es
        # findet dann KEINE tatsaechliche Neu-Navigation statt (anders als
        # bei einem waermeren location.reload() aus der Seite selbst). Ohne
        # den Cache-Buster wuerde das Fenster nach dem allerersten Scan
        # dauerhaft auf dem Ladebildschirm "Wird geladen ..." haengen
        # bleiben, weil url hier identisch zur bereits geladenen URL waere.
        # Bewusst KEINE kuenstliche Mindestanzeigedauer fuer den
        # Splash-Screen: Ist der Ordner klein oder komplett gecacht, darf
        # das Einlesen auch mal so schnell sein, dass der Splash praktisch
        # nicht sichtbar wird - das ist dann einfach ehrliches Verhalten,
        # kein Fehler, den man kuenstlich verstecken muesste.
        window.load_url(f"{url}?_r={time.time_ns()}")

    # Fenstergroesse/-position an die aktuelle Bildschirmaufloesung anpassen:
    # ohne explizites screen= verlaesst man sich auf WinForms'
    # FormStartPosition.CenterScreen, das in der Praxis (Mehrschirm-Setups,
    # DPI-Skalierung) beobachtbar nicht immer denselben, zentrierten Punkt
    # trifft. Deshalb wird der Hauptbildschirm ueber webview.screens()
    # bestimmt, die Fenstergroesse darauf begrenzt (kleiner Rand fuer
    # Taskleiste/Fensterrahmen) und explizit als screen= uebergeben - das
    # zentriert pywebview intern zuverlaessig selbst (siehe winforms.py).
    #
    # webview.screens[0] ist NICHT zuverlaessig der Hauptmonitor: die Liste
    # kommt aus WinForms' Screen.AllScreens, dessen Reihenfolge von der
    # Erkennungsreihenfolge der Grafikkarte abhaengt, nicht davon, welcher
    # Bildschirm in den Windows-Anzeigeeinstellungen als "Hauptmonitor"
    # gesetzt ist (beobachtet: Fenster oeffnete bei einem Nutzer mit zwei
    # Monitoren zuverlaessig auf dem NEBENmonitor). Windows platziert den
    # tatsaechlichen Hauptmonitor immer bei den virtuellen Desktop-
    # Koordinaten (0, 0); alle anderen Monitore haben davon abweichende
    # (auch negative) Koordinaten, je nach Anordnung. Deshalb wird hier
    # gezielt der Bildschirm mit x=0/y=0 gesucht, statt einfach den ersten
    # der Liste zu nehmen.
    try:
        screens = webview.screens
        primary_screen = next((s for s in screens if s.x == 0 and s.y == 0), screens[0])
        screen_w, screen_h = primary_screen.width, primary_screen.height
    except Exception:
        primary_screen = None
        screen_w, screen_h = 1680, 1020
    win_width = min(1680, max(1100, screen_w - 60))
    win_height = min(1020, max(700, screen_h - 90))

    try:
        window = webview.create_window(
            "AstroLogbuch", url, js_api=api,
            width=win_width, height=win_height, min_size=(1100, 700),
            screen=primary_screen)
    except Exception:
        traceback.print_exc()
        print("Konnte kein Programmfenster erstellen, verwende den Browser-Modus.")
        return False
    api._window = window

    def on_start():
        # Alles hier drin passiert in einem Hintergrundthread, erst nachdem
        # das Fenster sichtbar ist (so verlangt es pywebview fuer
        # create_file_dialog). Ein try/except um den gesamten Ablauf sorgt
        # dafuer, dass ein unerwarteter Fehler (z. B. eine kuenftige
        # pywebview-Version mit leicht anderer API) als lesbare Fehlerseite
        # IM Fenster erscheint, statt das Fenster stumm leer/haengend zu
        # lassen - eine Konsole ist in der App-Ansicht ja nicht garantiert
        # sichtbar.
        try:
            current_root = ROOT_FOLDER
            if not current_root or not os.path.isdir(current_root):
                chosen = pick_folder_dialog(window, current_root)
                if not chosen:
                    state["html_bytes"] = render_status_page(
                        "Kein Ordner ausgewählt",
                        detail="Über das Zahnrad-Symbol oben rechts kannst du jederzeit "
                               "einen Astro-Ordner auswählen.").encode("utf-8")
                    reload_window()
                    return
                current_root = chosen

            cfg = dict(config)
            cfg["root_folder"] = current_root
            result = api.apply_settings(cfg, progress_cb=progress_cb)
            if not result.get("ok"):
                state["html_bytes"] = render_status_page(
                    "Einlesen fehlgeschlagen", detail=result.get("error", "")).encode("utf-8")
            reload_window()
        except Exception:
            tb = traceback.format_exc()
            traceback.print_exc()
            state["html_bytes"] = render_status_page(
                "Unerwarteter Fehler beim Start", detail=tb).encode("utf-8")
            try:
                reload_window()
            except Exception:
                pass

    # Fenster-/Taskleisten-Icon: ohne explizite Angabe extrahiert WinForms es
    # aus sys.executable (siehe winforms.py: ExtractIconW). Als gebaute EXE
    # (pyinstaller --icon=..., siehe Schritt 2 in ANLEITUNG.txt) IST
    # sys.executable die EXE selbst - der Fallback liefert dann von sich aus
    # bereits das richtige Icon, eine zusaetzliche .ico-Datei neben der EXE
    # ist dafuer nicht noetig (die EXE ist dadurch alleine weitergebbar).
    # Nur im Dev-Betrieb ("py astro_dashboard.py") ist sys.executable der
    # Python-Interpreter (generisches Icon) - dort wird die .ico-Datei neben
    # dem Skript weiterhin explizit angegeben, falls vorhanden.
    icon_path = os.path.join(out_dir, ICON_FILENAME)
    is_frozen = getattr(sys, "frozen", False)
    webview_start_kwargs = {"icon": icon_path} if not is_frozen and os.path.isfile(icon_path) else {}
    webview.start(on_start, **webview_start_kwargs)
    return True


# ======================================================================
# Browser-Modus (Fallback, falls pywebview fehlt oder nicht funktioniert)
# ======================================================================

def run_legacy_browser_mode(out_dir, thumb_cache_path, object_cache_path):
    if not ROOT_FOLDER or not os.path.isdir(ROOT_FOLDER):
        print(f"FEHLER: Ordner nicht gefunden: {ROOT_FOLDER!r}")
        print("Bitte den Ordner in den Einstellungen (App-Ansicht) waehlen, oder")
        print(f"das Feld \"root_folder\" in {CONFIG_FILENAME} von Hand eintragen.")
        input("\nEnter zum Beenden...")
        return

    try:
        html_content, count = run_scan_and_build(out_dir, thumb_cache_path, object_cache_path)
    except Exception:
        traceback.print_exc()
        input("\nEin Fehler ist beim Einlesen aufgetreten (siehe oben). Enter zum Beenden...")
        return

    state = {"html_bytes": html_content.encode("utf-8"), "root_folder": ROOT_FOLDER}
    # Ueber einen lokalen Server statt direkt per file://-Link oeffnen, damit
    # ein Klick auf eine Zeile im Dashboard den Ordner tatsaechlich im
    # Explorer oeffnen kann (siehe Kommentar bei make_dashboard_handler()).
    handler_cls = make_dashboard_handler(state)
    try:
        server = http.server.HTTPServer(("127.0.0.1", 0), handler_cls)
    except OSError:
        output_html = os.path.join(out_dir, "AstroLogbuch.html")
        print("Konnte keinen lokalen Server starten, oeffne stattdessen nur die Datei.")
        print("Ein Klick auf eine Zeile kopiert dann nur den Pfad in die Zwischenablage.")
        try:
            webbrowser.open("file://" + output_html.replace("\\", "/"))
        except Exception:
            print("Konnte Browser nicht automatisch oeffnen. Bitte die Datei manuell oeffnen:")
            print(output_html)
        return

    port = server.server_address[1]
    url = f"http://127.0.0.1:{port}/"
    print(f"Dashboard erreichbar unter: {url}", flush=True)
    print("Dieses Fenster bitte offen lassen, solange du im Dashboard arbeitest -", flush=True)
    print("nur so kann ein Klick auf eine Zeile den Ordner direkt oeffnen.", flush=True)
    print("Zum Beenden dieses Fenster schliessen oder Strg+C druecken.\n", flush=True)

    try:
        webbrowser.open(url)
    except Exception:
        print("Konnte Browser nicht automatisch oeffnen. Bitte die Adresse manuell aufrufen:")
        print(url)

    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nBeendet.")


# ======================================================================
# main
# ======================================================================

def main():
    print(f"AstroLogbuch v{APP_VERSION}", flush=True)
    out_dir = os.path.dirname(os.path.abspath(sys.argv[0]))
    config_path = os.path.join(out_dir, CONFIG_FILENAME)
    thumb_cache_path = os.path.join(out_dir, THUMB_CACHE_FILENAME)
    object_cache_path = os.path.join(out_dir, OBJECT_CACHE_FILENAME)

    config = load_config(config_path)
    apply_config(config)

    if SHOW_THUMBNAILS and not HAVE_PIL:
        print("Hinweis: Paket 'Pillow' nicht gefunden, Vorschaubilder werden übersprungen.", flush=True)
        print("Für Vorschaubilder einmalig: pip install pillow\n", flush=True)

    if not try_launch_webview(config, config_path, thumb_cache_path, object_cache_path, out_dir):
        run_legacy_browser_mode(out_dir, thumb_cache_path, object_cache_path)


if __name__ == "__main__":
    try:
        main()
    except Exception:
        traceback.print_exc()
        input("\nEin Fehler ist aufgetreten (siehe oben). Enter zum Beenden...")
