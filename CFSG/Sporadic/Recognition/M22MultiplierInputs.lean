module

public import CFSG.Sporadic.Recognition.CoverRecipe

public section

namespace CFSG.Sporadic.Recognition.M22Multiplier

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Sporadic.Bridge.TwoGen.Native
  CFSG.Sporadic.Recognition.CoverRecipe CFSG.Sporadic.Th.Native

@[expose] def tabA : Table :=
  #[12, 7, 15, 11, 4, 21, 16, 1, 9, 8, 13, 3, 0, 10, 14, 2, 6, 17, 18, 19, 20, 5]

@[expose] def tabB : Table :=
  #[21, 17, 20, 12, 11, 10, 14, 13, 8, 7, 6, 4, 1, 19, 5, 15, 18, 3, 16, 9, 0, 2]

@[expose] def tabBi : Table :=
  #[20, 12, 21, 17, 11, 14, 10, 9, 8, 19, 5, 4, 3, 7, 6, 15, 18, 1, 16, 13, 2, 0]

@[expose] def m22Word (l : List ℤ) : List (Fin 2 × Bool) := l.map abLetter

@[expose] def m22Rels : List (List (Fin 2 × Bool)) :=
  [m22Word [1, 1, 1, 1, 2, -1, 2, -1, 2], m22Word [1, 1, 2, -1, -2, 1, 2, 2, -1, -2],
    m22Word (List.replicate 11 2), m22Word (List.replicate 5 1),
    m22Word (List.replicate 3 [1, -2]).flatten, m22Word (List.replicate 5 [1, 2, 2]).flatten]

@[expose] def m22B11 : List (Fin 2 × Bool) := m22Word (List.replicate 11 2)

@[expose] def m22Comm : Fin 2 → List (List (Fin 2 × Bool) × List (Fin 2 × Bool))
  | 0 => [(m22Word [-2, -1, 2], m22Word [-1]), (m22Word [1, 2], m22Word [1, 1, -2])]
  | 1 => [(m22Word [1, -2, -2], m22Word [-1, -1, -2, -1, 2])]

@[expose] def m22CommWord (i : Fin 2) : List (Fin 2 × Bool) := commWords (m22Comm i)

@[expose] def m22CommW (i : Fin 2) : FreeGroup (Fin 2) := FreeGroup.mk (m22CommWord i)

abbrev m22Cover : List (List (Fin 2 × Bool)) := coverWords m22Rels m22CommWord

abbrev M22Cover : Type := PresentedCover (wordSet m22Rels) m22CommW

@[expose] def m22GenWords : List (List (Fin 2 × Bool)) :=
  [m22Word [1, 2, 2, 1, 2, 1, -2, 1, 2, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2],
    m22Word [1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, -2, 1, -2, 1]]

@[expose] def m22SurjA : List (Fin 2 × Bool) :=
  m22Word [1, 2, 2, 1, 1, -2, -2, -1, -2, -2, 1, 2, 2, 1, 2, -1]

@[expose] def m22SurjB : List (Fin 2 × Bool) :=
  m22Word [2, 2, 1, -2, -2, 1, 1, 2, 2, 2, 1, -2, 1, 2]

@[expose] def m22CheckWords : List (List (Fin 2 × Bool)) :=
  m22Rels.map (substWord m22GenWords) ++
    (List.finRange 2).map (fun i => substWord m22GenWords ((i, false) :: m22CommWord i)) ++
    [substWord m22GenWords m22SurjA ++ [(0, false)], substWord m22GenWords m22SurjB ++ [(1, false)]]

@[noinline, expose] def m22TabCheck : Bool :=
  relCheck 22 tabA tabA tabB tabBi (m22CheckWords.map natWord)

end CFSG.Sporadic.Recognition.M22Multiplier
