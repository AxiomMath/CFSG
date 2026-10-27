module

public import Mathlib.Data.Fin.VecNotation

public section

namespace CFSG.Monster.Schur.M24

@[expose] def a2 : List (Fin 2 × Bool) := [(0, true), (0, true)]

@[expose] def b3 : List (Fin 2 × Bool) := [(1, true), (1, true), (1, true)]

@[expose] def ab23 : List (Fin 2 × Bool) := (List.replicate 23 [(0, true), (1, true)]).flatten

@[expose] def r4 : List (Fin 2 × Bool) :=
  (List.replicate 12 [(0, false), (1, false), (0, true), (1, true)]).flatten

@[expose] def r5 : List (Fin 2 × Bool) :=
  (List.replicate 5 [(0, false), (1, false), (0, false), (1, false), (0, true), (1, true),
    (0, true), (1, true)]).flatten

@[expose] def r6 : List (Fin 2 × Bool) :=
  [(0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true),
   (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true),
   (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false),
   (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true),
   (0, true), (1, false), (0, true), (1, false)]

@[expose] def r7 : List (Fin 2 × Bool) :=
  (List.replicate 4 [(0, true), (1, true), (0, true), (1, true), (0, true), (1, false),
    (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true),
    (1, false)]).flatten

@[expose] def U : List (List (Fin 2 × Bool)) := [b3, ab23]

@[expose] def T : Fin 4 → List (Fin 2 × Bool) := ![a2, r5, r6, r7]

end CFSG.Monster.Schur.M24
