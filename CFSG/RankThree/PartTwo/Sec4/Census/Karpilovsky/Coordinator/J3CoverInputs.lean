module

public import CFSG.LieType.Multipliers.CoverWords
public import CFSG.Sporadic.Recognition.CoverRecipe

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.J3Cover

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Sporadic.Recognition.CoverRecipe

@[expose] def ofCodes (c : List ℕ) : List (Fin 3 × Bool) :=
  c.map fun x => (⟨x / 2 % 3, Nat.mod_lt _ (by norm_num)⟩, decide (x % 2 = 0))

@[expose] def relCodes : List (List ℕ) :=
  [[0, 0],
  [2, 2, 2],
  [3, 4, 0, 4, 0, 5],
  [2, 0, 2, 0, 3, 0, 3, 0, 3, 0, 2, 0, 2, 0, 3, 0, 3, 0, 3, 0, 2, 0, 2, 0, 3, 0, 3, 0, 3, 0],
  [2, 0, 3, 0, 2, 0, 3, 0, 3, 0, 2, 0, 3, 0, 3, 0, 2, 0, 3, 0, 2, 0, 3, 0, 3, 0, 2, 0, 3, 0, 3,
   0],
  [0, 4, 0, 4, 0, 4, 0, 4, 0, 4, 0, 4, 0, 4, 0, 4, 0, 4, 0, 4, 0, 4, 0, 4, 0, 4, 0, 4, 0, 4, 0,
   4, 0, 4, 0, 4, 0, 4],
  [0, 4, 0, 4, 0, 4, 0, 4, 0, 4, 0, 4, 0, 5, 0, 5, 0, 5, 0, 5, 0, 5, 0, 4, 0, 4, 0, 4, 0, 4, 0,
   4, 0, 4, 0, 5, 0, 5, 0, 5, 0, 5, 0, 5],
  [0, 4, 0, 4, 0, 5, 0, 4, 0, 4, 0, 5, 0, 4, 0, 5, 0, 5, 0, 4, 0, 5, 0, 4, 0, 4, 0, 5, 0, 4, 0,
   4, 0, 5, 0, 4, 0, 5, 0, 5, 0, 4, 0, 5],
  [0, 4, 0, 4, 0, 4, 0, 5, 0, 4, 0, 5, 0, 4, 0, 5, 0, 4, 0, 4, 0, 4, 0, 5, 0, 4, 0, 5, 0, 4, 0,
   5, 0, 4, 0, 5, 0, 5, 0, 4, 0, 5, 0, 4, 0, 5, 0, 4, 0, 5]]

@[expose] def rels : List (List (Fin 3 × Bool)) := relCodes.map ofCodes

@[expose] def commCodes : Fin 3 → List (List ℕ × List ℕ)
  | 0 => [([2, 0, 2, 0, 2, 0, 3, 0, 3], [2, 0, 2, 0, 2, 0, 3, 0, 3, 0])]
  | 1 => [([0, 2, 0, 3, 0, 3], [0, 2, 0, 3, 0, 2, 0, 3, 0, 2])]
  | 2 => [([5], [2, 0, 2, 0, 3, 0, 3])]

@[expose] def commWord (i : Fin 3) : List (Fin 3 × Bool) :=
  commWords ((commCodes i).map fun p => (ofCodes p.1, ofCodes p.2))

abbrev cover : List (List (Fin 3 × Bool)) := coverWords rels commWord

@[expose] def coverS : List (List (Fin 3 × Bool)) :=
  cover.mergeSort fun u v => decide (u.length ≤ v.length)

@[expose] def walkWord : List (Fin 3 × Bool) := ofCodes (List.replicate 19 [0, 4]).flatten

@[expose] def genWords : List (List (Fin 2 × Bool)) :=
  [[(0, true)], [(1, true), (0, true), (1, true), (0, true), (1, false)], [(1, true)]]

@[expose] def checkWords : List (List (Fin 3 × Bool)) :=
  rels ++ (List.finRange 3).map fun i => (i, false) :: commWord i

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.J3Cover
