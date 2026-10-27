module

public import CFSG.LocalAnalysis.SteinbergCCHSData
public import CFSG.Certificates.WordSubgroup

public section

namespace CFSG.LocalAnalysis.HigmanSimsCover

open CFSG.CosetTable CFSG.LieType.Multipliers

@[expose] def substAB (w : List (Fin 3 × Bool)) : List (Fin 2 × Bool) := substWord genWords w

@[expose] def hsWords : List (List (Fin 2 × Bool)) :=
  rels.map substAB ++
    (List.finRange 3).map (fun i => substAB (commWords (pairs i) ++ [(i, false)])) ++
    [substAB (abWords.getD 0 []) ++ [(0, false)], substAB (abWords.getD 1 []) ++ [(1, false)]]

end CFSG.LocalAnalysis.HigmanSimsCover
