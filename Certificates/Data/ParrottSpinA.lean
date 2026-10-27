module

public import Certificates.Data.ParrottSpin
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43ModelData
public import CFSG.GH74.KGroups.Generic

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.KGroups

@[expose] def conjWordX : List Bool := [false]

@[expose] def conjWordY : List Bool :=
  [true, true, true, false, true, false, true, true, false, true, true, true, false, true, false,
    true, true, false, true, true, false, true, true, false, true, true, true]

@[expose] def toSpinWord (w : List Bool) : List (Fin 2 × Bool) :=
  w.map fun b => if b then (1, true) else (0, true)

@[expose] def bitConj (M N : Matrix (Fin 8) (Fin 8) (ZMod 2)) (mask : Nat) : Nat :=
  bitRow M (bitRow N (bitRow M mask))

@[expose] def bitSq (M : Matrix (Fin 8) (Fin 8) (ZMod 2)) (mask : Nat) : Nat :=
  bitRow M (bitRow M mask)

end CFSG.RankThree.GF2n.Parrott
