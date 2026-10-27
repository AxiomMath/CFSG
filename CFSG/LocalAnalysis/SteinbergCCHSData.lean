module

public import CFSG.LieType.Multipliers.CoverWords

public section

namespace CFSG.LocalAnalysis.HigmanSimsCover

open CFSG.LieType.Multipliers

@[expose] def parseAB (s : String) : List (Fin 2 × Bool) :=
  s.toList.filterMap fun c =>
    if c = 'a' then some (0, true) else if c = 'A' then some (0, false)
    else if c = 'b' then some (1, true) else if c = 'B' then some (1, false) else none

@[expose] def parseXYT (s : String) : List (Fin 3 × Bool) :=
  s.toList.filterMap fun c =>
    if c = 'x' then some (0, true) else if c = 'X' then some (0, false)
    else if c = 'y' then some (1, true) else if c = 'Y' then some (1, false)
    else if c = 't' then some (2, true) else if c = 'T' then some (2, false) else none

@[expose] def genWords : List (List (Fin 2 × Bool)) :=
  ["BabbaBBab", "ababaBaBabaB", "Bab"].map parseAB

@[expose] def rels : List (List (Fin 3 × Bool)) :=
  ["xx", "yyyy", "xyxyxyxyxyxyxyxyxyxyxy", "xyyxyyxyyxyyxyyxyy", "xyxyxYxyxyyxYxyxYxY", "tt",
    "txyyxyxYxyxytXyXyXyXYXYXY", "txyxyxYxyyxYxYxYtyXYXyXYYXyXYXY", "tYxytYXytYxy",
    "tyytYxyxYxyxyytYYtYxyxYxyxyy"].map parseXYT

@[expose] def pairs : Fin 3 → List (List (Fin 3 × Bool) × List (Fin 3 × Bool))
  | 0 => [(parseXYT "YxYxy", parseXYT "yxyyxYxyyxYx")]
  | 1 => [(parseXYT "xyxY", parseXYT "xyyxyxyyxyxyxy")]
  | 2 => [(parseXYT "yytyytyy", parseXYT "ytytYtytYty")]

@[expose] def coverWs : List (List (Fin 3 × Bool)) := coverWords rels fun i => commWords (pairs i)

@[expose] def abWords : List (List (Fin 3 × Bool)) :=
  ["xyxYxtytyxYx", "YtxYxyxyxtyyxytYxYtx"].map parseXYT

@[expose] def kerWord : List (Fin 3 × Bool) := parseXYT "tyytYxyxYxyxyytYYtYxyxYxyxyy"

theorem kerWord_mem : kerWord ∈ rels :=
  List.mem_map_of_mem (f := parseXYT) (by simp)

end CFSG.LocalAnalysis.HigmanSimsCover
