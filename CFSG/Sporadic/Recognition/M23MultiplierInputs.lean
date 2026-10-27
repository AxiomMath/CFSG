module

public import CFSG.Sporadic.Recognition.CoverRecipe
public import CFSG.Sporadic.Bridge.M23SurjInputs

public section

namespace CFSG.Sporadic.Recognition.M23Multiplier

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Sporadic.Bridge.TwoGen.Native
  CFSG.Sporadic.Bridge.M23 CFSG.Sporadic.Recognition.CoverRecipe

@[expose] def m23Pos (c : List ℕ) : List (Fin 6 × Bool) :=
  c.map fun x => (⟨x % 6, Nat.mod_lt _ (by norm_num)⟩, true)

@[expose] def m23Pow (k : ℕ) (c : List ℕ) : List (Fin 6 × Bool) :=
  m23Pos (List.replicate k c).flatten

@[expose] def m23Label (i j : ℕ) : ℕ :=
  if i = 0 ∧ j = 1 then 3 else if i = 1 ∧ j = 2 then 5 else if i = 2 ∧ j = 3 then 3
  else if i = 3 ∧ j = 4 then 3 else if i = 2 ∧ j = 4 then 4 else if i = 1 ∧ j = 5 then 3
  else if i = 3 ∧ j = 5 then 3 else 2

@[expose] def m23Coxeter : List (List (Fin 6 × Bool)) :=
  (List.finRange 6).map (fun i => [(i, true), (i, true)]) ++
    (List.finRange 6).flatMap fun i => ((List.finRange 6).filter fun j => i.val < j.val).map
      fun j => (List.replicate (m23Label i.val j.val) [(i, true), (j, true)]).flatten

@[expose] def m23Extra : List (List (Fin 6 × Bool)) :=
  [m23Pos [0, 2, 4, 2, 4], m23Pow 5 [1, 2, 3], m23Pow 5 [1, 2, 3, 5]]

@[expose] def m23Rels : List (List (Fin 6 × Bool)) := m23Coxeter ++ m23Extra

@[expose] def m23CommCodes : Fin 6 → List (List ℕ × List ℕ)
  | 0 => [([2], [4])]
  | 1 => [([0], [1]), ([2], [4])]
  | 2 => [([1], [0]), ([4, 2, 1, 2], [1])]
  | 3 => [([1], [2]), ([1, 3], [2, 1, 2])]
  | 4 => [([2], [1]), ([3, 2, 1, 2], [1, 0, 3, 4])]
  | 5 => [([1], [5]), ([4], [0, 1, 2])]

@[expose] def m23Comm (i : Fin 6) : List (List (Fin 6 × Bool) × List (Fin 6 × Bool)) :=
  (m23CommCodes i).map fun p => (m23Pos p.1, m23Pos p.2)

@[expose] def m23CommWord (i : Fin 6) : List (Fin 6 × Bool) := commWords (m23Comm i)

@[expose] def m23CommW (i : Fin 6) : FreeGroup (Fin 6) := FreeGroup.mk (m23CommWord i)

abbrev m23Cover : List (List (Fin 6 × Bool)) := coverWords m23Rels m23CommWord

abbrev M23Cover : Type := PresentedCover (wordSet m23Rels) m23CommW

abbrev m23Rels5 := restrictWords (subsetOf _ [0, 1, 2, 3, 4]) m23Rels

abbrev m23Cover5 := restrictWords (subsetOf _ [0, 1, 2, 3, 4]) m23Cover

@[expose] def m23GenWords : List (List (Fin 2 × Bool)) :=
  [[2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, -2], [1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, -2, 1],
    [2, 1, -2, 1, 2, 2, 1, 2, 1, -2], [2, 1, 2, 1, 2, 2, 1, -2, 1, -2],
    [1, 2, 1, 2, 1, 2, 2, 1, -2, 1, -2, 1],
    [1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, -2, 1, -2, 1, -2, 1]].map (List.map abLetter)

@[expose] def m23SurjA : List (Fin 6 × Bool) := m23Pos [0, 1, 0, 3, 4, 3]

@[expose] def m23SurjB : List (Fin 6 × Bool) :=
  m23Pos [5, 1, 2, 3, 2, 1, 2, 4, 5, 3, 2, 1, 0, 5, 1, 2, 4, 3]

@[expose] def m23CheckWords : List (List (Fin 2 × Bool)) :=
  m23Rels.map (substWord m23GenWords) ++
    (List.finRange 6).map (fun i => substWord m23GenWords ((i, false) :: m23CommWord i)) ++
    [substWord m23GenWords m23SurjA ++ [(0, false)], substWord m23GenWords m23SurjB ++ [(1, false)]]

@[noinline, expose] def m23TabCheck : Bool :=
  relCheck 23 tabA tabA tabBi tabB (m23CheckWords.map natWord)

end CFSG.Sporadic.Recognition.M23Multiplier
