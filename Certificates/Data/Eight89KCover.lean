module

public import CFSG.Certificates.CosetTablePresented
public import Mathlib

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KData

open CFSG.CosetTable

@[expose] def coverWords (n i j k l : Nat) : List (List (Fin 3 × Bool)) :=
  [List.replicate n (2, true),
    [(0, false), (2, false), (0, true), (2, true)],
    [(1, false), (2, false), (1, true), (2, true)],
    [(0, true), (0, true)] ++ List.replicate (3 * i) (2, false),
    List.replicate 4 (1, true) ++ List.replicate (3 * j) (2, false),
    (List.replicate 5 [(0, true), (1, true)]).flatten ++ List.replicate k (2, false),
    (List.replicate 5 [(0, true), (1, true), (1, true)]).flatten ++ List.replicate l (2, false)]

@[expose] def cover3Orders : List (Nat × Nat × Nat) :=
  [(0, 0, 1080), (0, 1, 360), (0, 2, 360), (1, 0, 1080), (1, 1, 360), (1, 2, 360)]

@[expose] def cover6Orders : List (Nat × Nat × Nat × Nat × Nat) :=
  [(0, 0, 0, 0, 2160), (0, 0, 0, 1, 720), (0, 0, 0, 2, 720),
    (0, 0, 1, 0, 2160), (0, 0, 1, 1, 720), (0, 0, 1, 2, 720),
    (0, 1, 0, 0, 1080), (0, 1, 0, 1, 360), (0, 1, 0, 2, 360),
    (0, 1, 1, 0, 1080), (0, 1, 1, 1, 360), (0, 1, 1, 2, 360),
    (1, 0, 0, 0, 1080), (1, 0, 0, 1, 360), (1, 0, 0, 2, 360),
    (1, 0, 1, 0, 1080), (1, 0, 1, 1, 360), (1, 0, 1, 2, 360),
    (1, 1, 0, 0, 2160), (1, 1, 0, 1, 720), (1, 1, 0, 2, 720),
    (1, 1, 1, 0, 2160), (1, 1, 1, 1, 720), (1, 1, 1, 2, 720)]

@[expose] def cover3EnumCheck (_ : Unit := ()) : Bool :=
  cover3Orders.all fun c => subsetCheck (coverWords 3 0 0 c.1 c.2.1) [] 50000 c.2.2

@[expose] def cover6EnumCheck (_ : Unit := ()) : Bool :=
  cover6Orders.all fun c =>
    subsetCheck (coverWords 6 c.1 c.2.1 c.2.2.1 c.2.2.2.1) [] 50000 c.2.2.2.2

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KData
