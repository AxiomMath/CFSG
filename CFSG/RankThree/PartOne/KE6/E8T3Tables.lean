module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartOne.KE6.E8T3Engine

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Lattice
  CFSG.LieType.Steinberg.Adjoint

@[expose] def e8Edges : List (Fin Tag.E8.rank × Fin Tag.E8.rank) :=
  [(0, 2), (1, 3), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7)]

@[expose] def e8TwoA2 :
    List (Fin Tag.E8.rank × Fin Tag.E8.rank × Fin Tag.E8.rank × Fin Tag.E8.rank) :=
  [(0, 2, 4, 5), (0, 2, 5, 6), (0, 2, 6, 7), (1, 3, 5, 6), (1, 3, 6, 7), (2, 3, 5, 6),
   (2, 3, 6, 7), (3, 4, 6, 7)]

@[expose] def rotCols (a b : Fin Tag.E8.rank) : List (List V8) :=
  [[(Pi.single b 1 : V8), -((Pi.single a 1 : V8) + (Pi.single b 1 : V8))],
   [-((Pi.single a 1 : V8) + (Pi.single b 1 : V8)), (Pi.single a 1 : V8)]]

@[expose] def rot2Cols (a b c d : Fin Tag.E8.rank) : List (List V8) :=
  (rotCols a b).flatMap fun r => (rotCols c d).map fun s => r ++ s

@[expose] def e8D4Table : List (List (List ℤ) × List (Fin Tag.E8.rank) × List (Fin Tag.E8.rank) ×
    (Fin Tag.E8.rank × Fin Tag.E8.rank × Fin Tag.E8.rank)) :=
  [
   ([[0, -1, -1, -1, -1, 0, 0, 0], [0, 0, -1, -1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0]],
      [4, 3, 2, 1, 3, 4, 3, 1],
      [2, 1, 3, 2],
      (1, 4, 2)),
   ([[0, -1, -1, -1, -1, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, -1, -1, 0, 0, 0]],
      [2, 3, 4, 2, 1, 3, 2, 1],
      [1, 3, 4, 3],
      (1, 2, 4)),
   ([[0, -1, -1, -1, 0, 0, 0, 0], [0, 0, -1, -1, -1, 0, 0, 0], [0, 1, 1, 1, 1, 0, 0, 0], [0, -1, 0, -1, -1, 0, 0, 0]],
      [3, 2, 1, 3, 4, 3, 2, 1],
      [4, 2, 1, 3],
      (1, 4, 2)),
   ([[0, -1, -1, -1, 0, 0, 0, 0], [0, 1, 0, 1, 1, 0, 0, 0], [0, 0, 0, -1, -1, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0]],
      [2, 3, 4, 3, 2, 1, 3, 2],
      [1, 3, 4, 1],
      (1, 2, 4)),
   ([[0, -1, 0, -1, -1, 0, 0, 0], [0, -1, -1, -1, 0, 0, 0, 0], [0, 1, 1, 1, 1, 0, 0, 0], [0, 0, -1, -1, -1, 0, 0, 0]],
      [3, 2, 1, 3, 4, 3, 2, 1],
      [4, 2, 1, 3],
      (1, 2, 4)),
   ([[0, -1, 0, -1, -1, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, -1, -1, 0, 0, 0, 0], [0, 1, 1, 1, 0, 0, 0, 0]],
      [4, 3, 2, 1, 3, 4, 1, 3],
      [1, 3, 2, 1],
      (1, 4, 2)),
   ([[0, -1, 0, -1, 0, 0, 0, 0], [0, -1, -1, -1, -1, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 1, 0, 0, 0, 0]],
      [4, 3, 2, 1, 3, 4, 3, 2],
      [2, 1, 3, 1],
      (1, 2, 4)),
   ([[0, -1, 0, -1, 0, 0, 0, 0], [0, 0, 0, 1, 1, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, -1, -1, -1, -1, 0, 0, 0]],
      [3, 2, 1, 3, 4, 1, 3, 2],
      [4, 1, 3, 1],
      (1, 4, 2)),
   ([[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, -1, -1, -1, 0, 0, 0], [0, -1, 0, -1, 0, 0, 0, 0], [0, 1, 1, 1, 0, 0, 0, 0]],
      [4, 3, 2, 1, 3, 4, 2, 3],
      [2, 3, 2, 1],
      (1, 2, 4)),
   ([[0, 0, 0, 1, 0, 0, 0, 0], [0, 1, 0, 1, 1, 0, 0, 0], [0, -1, 0, -1, 0, 0, 0, 0], [0, 0, -1, -1, -1, 0, 0, 0]],
      [2, 1, 3, 4, 2, 1, 3, 2],
      [3, 4, 3, 1],
      (1, 4, 2)),
   ([[0, 0, 0, 1, 1, 0, 0, 0], [0, 0, -1, -1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, -1, -1, -1, -1, 0, 0, 0]],
      [3, 2, 1, 3, 4, 2, 3, 1],
      [4, 2, 3, 2],
      (1, 2, 4)),
   ([[0, 0, 0, 1, 1, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0], [0, -1, -1, -2, -1, 0, 0, 0], [0, 0, 1, 1, 0, 0, 0, 0]],
      [2, 1, 3, 4, 3, 2, 1, 3],
      [3, 4, 2, 1],
      (1, 4, 2)),
   ([[0, 0, 1, 1, 0, 0, 0, 0], [0, -1, -1, -1, -1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, -1, -1, 0, 0, 0]],
      [1, 3, 4, 2, 1, 3, 2, 1],
      [2, 3, 4, 3],
      (1, 4, 2)),
   ([[0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 1, 1, 0, 0, 0], [0, -1, -1, -2, -1, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0]],
      [2, 1, 3, 4, 3, 2, 1, 3],
      [3, 4, 2, 1],
      (1, 2, 4)),
   ([[0, 0, 1, 1, 1, 0, 0, 0], [0, -1, -1, -1, 0, 0, 0, 0], [0, 0, 0, -1, -1, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0]],
      [1, 3, 4, 3, 2, 1, 3, 1],
      [2, 3, 4, 2],
      (1, 4, 2)),
   ([[0, 0, 1, 1, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, -1, -1, 0, 0, 0, 0], [0, -1, 0, -1, -1, 0, 0, 0]],
      [2, 1, 3, 4, 2, 1, 3, 1],
      [3, 4, 3, 2],
      (1, 2, 4))]

@[expose] def d4Cols : List (List V8) := e8D4Table.map fun e => e.1.map (toVec Tag.E8.rank)

@[expose] def d4a2Cols : List (List V8) :=
  d4Cols.flatMap fun c => (rotCols 6 7).map fun r => c ++ r

set_option maxRecDepth 100000 in
theorem e8T3_search_A2 : ∀ e ∈ e8Edges, tsearch (e8RootsIn [e.1, e.2]) [e.1, e.2] []
    (fun part => !relOK part || (part.map Prod.snd ∈ rotCols e.1 e.2)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem e8T3_search_2A2 : ∀ q ∈ e8TwoA2, tsearch (e8RootsIn [q.1, q.2.1, q.2.2.1, q.2.2.2])
    [q.1, q.2.1, q.2.2.1, q.2.2.2] []
    (fun part => !relOK part || (part.map Prod.snd ∈ rot2Cols q.1 q.2.1 q.2.2.1 q.2.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem e8T3_search_D4 : tsearch (e8RootsIn [1, 2, 3, 4]) [1, 2, 3, 4] []
    (fun part => !relOK part || (part.map Prod.snd ∈ d4Cols)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem e8T3_search_D4A2 : tsearch (e8RootsIn [1, 2, 3, 4, 6, 7]) [1, 2, 3, 4, 6, 7] []
    (fun part => !relOK part || (part.map Prod.snd ∈ d4a2Cols)) = true := by
  decide +kernel

end CFSG.RankThree.PartOne.KE6
