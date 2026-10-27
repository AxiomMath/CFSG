module

public import CFSG.Sporadic.Recognition.CoverRecipe
public import Certificates.Data.CFSGNative.HS.Data

public section

namespace CFSG.Sporadic.Recognition.HSMultiplier

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Sporadic.Bridge.TwoGen.Native
  CFSG.Sporadic.Recognition.CoverRecipe
open CFSG.Sporadic.HS.Native (hsData)

@[expose] def hsPos (c : List ℕ) : List (Fin 6 × Bool) :=
  c.map fun x => (⟨x % 6, Nat.mod_lt _ (by norm_num)⟩, true)

@[expose] def hsPow (k : ℕ) (c : List ℕ) : List (Fin 6 × Bool) :=
  hsPos (List.replicate k c).flatten

@[expose] def hsLabel (i j : ℕ) : ℕ :=
  if i = 0 ∧ j = 1 then 3 else if i = 1 ∧ j = 2 then 5 else if i = 2 ∧ j = 3 then 3
  else if i = 3 ∧ j = 4 then 3 else if i = 2 ∧ j = 4 then 4 else if i = 0 ∧ j = 5 then 3
  else if i = 2 ∧ j = 5 then 3 else if i = 4 ∧ j = 5 then 3 else 2

@[expose] def hsCoxeter : List (List (Fin 6 × Bool)) :=
  (List.finRange 6).map (fun i => [(i, true), (i, true)]) ++
    (List.finRange 6).flatMap fun i => ((List.finRange 6).filter fun j => i.val < j.val).map
      fun j => (List.replicate (hsLabel i.val j.val) [(i, true), (j, true)]).flatten

@[expose] def hsExtra : List (List (Fin 6 × Bool)) :=
  [hsPos [0, 2, 4, 2, 4], hsPow 5 [1, 2, 3], hsPow 5 [0, 1, 2, 5], hsPow 5 [1, 3, 2, 5],
    hsPow 4 [0, 3, 2, 1, 2, 4, 5]]

@[expose] def hsRels : List (List (Fin 6 × Bool)) := hsCoxeter ++ hsExtra

@[expose] def hsCommCodes : Fin 6 → List (List ℕ × List ℕ)
  | 0 => [([2], [4])]
  | 1 => [([0], [1]), ([2], [4])]
  | 2 => [([1], [0]), ([4, 2, 1, 2], [1])]
  | 3 => [([1], [2]), ([1, 3], [2, 1, 2])]
  | 4 => [([2], [1]), ([3, 2, 1, 2], [1, 0, 3, 4])]
  | 5 => [([0, 2, 5, 0, 2], [0, 4, 5, 0, 4])]

@[expose] def hsComm (i : Fin 6) : List (List (Fin 6 × Bool) × List (Fin 6 × Bool)) :=
  (hsCommCodes i).map fun p => (hsPos p.1, hsPos p.2)

@[expose] def hsCommWord (i : Fin 6) : List (Fin 6 × Bool) := commWords (hsComm i)

@[expose] def hsCommW (i : Fin 6) : FreeGroup (Fin 6) := FreeGroup.mk (hsCommWord i)

abbrev hsCover : List (List (Fin 6 × Bool)) := coverWords hsRels hsCommWord

abbrev HSCover : Type := PresentedCover (wordSet hsRels) hsCommW

abbrev hsRels5 := restrictWords (subsetOf _ [0, 1, 2, 3, 4]) hsRels

abbrev hsCover5 := restrictWords (subsetOf _ [0, 1, 2, 3, 4]) hsCover

@[expose] def hsGenWords : List (List (Fin 2 × Bool)) :=
  [[1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, -2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2],
   [1, 2, 1, 2, 2, 1, -2, -2, 1, -2, 1, 2, 1, 2, 2, 1, -2, -2, 1, -2],
   [1, -2, -2, 1, 2, 1, -2, 1, -2, 1, 2, 2, 1, -2, -2, 1, 2, 1, 2, 1, -2, 1, 2, 2, 1],
   [1],
   [1, 2, 1, -2, 1, -2, 1, -2, -2, 1, 2, 1, 2, 2, 1, -2, -2, 1, -2, 1, -2, -2, 1, 2, 1, 2, 2, 1,
     -2, 1, -2],
   [-2, -2, 1, -2, 1, 2, 1, 2, 2, 1, -2, -2, 1, -2, 1, 2, 1, 2, 2]].map (List.map abLetter)

@[expose] def hsSurjA : List (Fin 6 × Bool) := hsPos [3]

@[expose] def hsSurjB : List (Fin 6 × Bool) :=
  hsPos [1, 0, 5, 2, 4, 5, 2, 3, 4, 2, 1, 2, 5, 0, 2, 1, 3, 2, 4]

@[expose] def hsCheckWords : List (List (Fin 2 × Bool)) :=
  hsRels.map (substWord hsGenWords) ++
    (List.finRange 6).map (fun i => substWord hsGenWords ((i, false) :: hsCommWord i)) ++
    [substWord hsGenWords hsSurjA ++ [(0, false)], substWord hsGenWords hsSurjB ++ [(1, false)]]

@[noinline, expose] def hsTabCheck : Bool :=
  vecRelCheck hsData (hsCheckWords.map natWord)

end CFSG.Sporadic.Recognition.HSMultiplier
