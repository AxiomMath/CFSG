module

public import CFSG.Sporadic.Recognition.McLMultiplierInputs
public import CFSG.Sporadic.Recognition.CoverRecipe
public import Certificates.Data.CFSGNative.Co2.Data

public section

namespace CFSG.Sporadic.Recognition.Co2Multiplier

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Sporadic.Bridge.TwoGen.Native
  CFSG.Sporadic.Recognition.CoverRecipe CFSG.Sporadic.Recognition.McLMultiplier
open CFSG.Sporadic.Co2.Native (co2Data)

@[expose] def co2Pos (c : List ℕ) : List (Fin 7 × Bool) :=
  c.map fun x => (⟨x % 7, Nat.mod_lt _ (by norm_num)⟩, true)

@[expose] def co2Pow (k : ℕ) (c : List ℕ) : List (Fin 7 × Bool) :=
  co2Pos (List.replicate k c).flatten

@[expose] def co2Embed (w : List (Fin 6 × Bool)) : List (Fin 7 × Bool) :=
  w.map fun l => (l.1.castSucc, l.2)

@[expose] def co2Extra : List (List (Fin 7 × Bool)) :=
  [co2Pos [6, 6], co2Pow 2 [0, 3, 6], co2Pow 2 [1, 3, 6], co2Pow 2 [1, 3, 4, 6],
    co2Pow 3 [2, 4, 2, 6], co2Pow 3 [2, 4, 3, 6], co2Pow 4 [3, 5, 6], co2Pow 3 [4, 5, 4, 6],
    co2Pow 4 [1, 2, 6, 4, 3, 2, 5]]

@[expose] def co2Rels : List (List (Fin 7 × Bool)) := mclRels.map co2Embed ++ co2Extra

@[expose] def co2CommCodes : Fin 7 → List (List ℕ × List ℕ)
  | 0 => [([2], [5])]
  | 1 => [([0], [1]), ([2], [5])]
  | 2 => [([1], [0]), ([5, 2, 1, 2], [1])]
  | 3 => [([1], [2]), ([1, 3], [2, 1, 2])]
  | 4 => [([1], [0, 4, 0])]
  | 5 => [([2], [1]), ([3, 2, 1, 2], [1, 0, 3, 5])]
  | 6 => [([1], [0]), ([5, 2, 1, 2], [1]), ([2], [2, 6])]

@[expose] def co2Comm (i : Fin 7) : List (List (Fin 7 × Bool) × List (Fin 7 × Bool)) :=
  (co2CommCodes i).map fun p => (co2Pos p.1, co2Pos p.2)

@[expose] def co2CommWord (i : Fin 7) : List (Fin 7 × Bool) := commWords (co2Comm i)

@[expose] def co2CommW (i : Fin 7) : FreeGroup (Fin 7) := FreeGroup.mk (co2CommWord i)

abbrev co2Cover : List (List (Fin 7 × Bool)) := coverWords co2Rels co2CommWord

@[expose] def co2Cover6 : List (List (Fin 6 × Bool)) :=
  restrictWords (subsetOf 7 [0, 1, 2, 3, 4, 5]) co2Cover

@[expose] def co2GenWords : List (List (Fin 2 × Bool)) :=
  [[1, -2, 1, -2, -2, 1, 2, 2, 1, 2, 2, 1, 2, 1, -2, -2, 1, 2, 2, 1, 2, 1, 2, 1, -2, 1, -2, -2, 1,
     -2, 1, 2, 1, 2, 1, -2, -2, 1, 2, 2, 1, -2, 1, -2, -2, 1, -2, -2, 1, 2, 2, 1, 2, 1],
   [1, -2, 1, 2, 1, 2, 2, 1, -2, 1, 2, 2, 1, 2, 1, -2, 1, 2, 2, 1, 2, 2, 1, -2, -2, 1, 2, 1, 2, 2,
     1, -2, -2, 1, -2, -2, 1, -2, 1, -2, -2, 1, 2, 1, -2, -2, 1, -2, -2, 1, 2, 1, 2, 1],
   [2, 1, 2, 1, 2, 1, -2, 1, 2, 2, 1, -2, 1, -2, 1, -2, -2, 1, 2, 2, 1, 2, 1, 2, 1, -2, -2, 1, -2,
     1, -2, 1, -2, 1, -2, -2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, -2, 1, -2, 1, -2],
   [2, 1, 2, 1, 2, 1, -2, -2, 1, 2, 1, 2, 1, 2, 1, -2, -2, 1, 2, 2, 1, 2, 1, -2, -2, 1, -2, -2, 1,
     -2, 1, -2, -2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, -2, 1, -2, -2, 1, 2, 2],
   [1, 2, 1, -2, -2, 1, 2, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2, -2, 1, -2, 1, 2, 1, 2,
     2, 1, 2, 1, -2, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2, -2, 1, 2, 2, 1, -2, 1],
   [-2, 1, -2, 1, -2, 1, -2, 1, 2, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 2, 1, 2,
     2, 1, -2, 1, -2, -2, 1, -2, -2, 1, -2, -2, 1, 2, 2, 1, -2, 1, 2, 2],
   [1, -2, -2, 1, 2, 2, 1, 2, 2, 1, -2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, -2, -2, 1, -2, 1, 2, 2,
     1, -2, -2, 1, -2, -2, 1, 2, 1, -2, 1, -2, -2, 1, 2, 1, -2, -2]].map (List.map abLetter)

@[expose] def co2SurjA : List (Fin 7 × Bool) :=
  co2Pos [3, 4, 2, 3, 5, 6, 5, 2, 4, 5, 6, 5, 3, 2, 1, 4, 0, 5, 3, 4, 5, 2, 3, 4, 5, 2, 4, 6]

@[expose] def co2SurjB : List (Fin 7 × Bool) :=
  co2Pos [0, 1, 5, 3, 4, 2, 1, 2, 1, 3, 5, 2, 4, 2, 6, 5, 3, 2, 1, 4, 5, 6, 2, 3, 5, 3, 2]

@[expose] def co2CheckWords : List (List (Fin 2 × Bool)) :=
  co2Rels.map (substWord co2GenWords) ++
    (List.finRange 7).map (fun i => substWord co2GenWords ((i, false) :: co2CommWord i)) ++
    [substWord co2GenWords co2SurjA ++ [(0, false)], substWord co2GenWords co2SurjB ++ [(1, false)]]

@[noinline, expose] def co2TabCheck : Bool :=
  vecRelCheck co2Data (co2CheckWords.map natWord)

end CFSG.Sporadic.Recognition.Co2Multiplier
