module

public section

namespace CFSG.Monster.Schur

@[expose] def m12R1 : List (Nat × Bool) :=
  [(1, false), (0, true), (1, false), (0, true), (1, false), (0, true)]

@[expose] def m12R2 : List (Nat × Bool) :=
  [(0, true), (0, true), (0, true), (0, true), (0, true), (1, true), (1, true), (1, true),
    (1, true), (1, true), (1, true)]

@[expose] def m12R3 : List (Nat × Bool) :=
  [(0, true), (1, true), (1, true), (0, true), (1, false), (0, true), (0, true), (1, true),
    (0, true), (0, true), (1, true), (1, true)]

@[expose] def m12Rels : List (List (Fin 3 × Bool)) :=
  [[(2, true), (2, true), (2, true)],
    [(2, true), (0, true), (2, false), (0, false)],
    [(2, true), (1, true), (2, false), (1, false)],
    [(1, false), (0, true), (1, false), (0, true), (1, false), (0, true), (2, false)],
    [(0, true), (0, true), (0, true), (0, true), (0, true), (1, true), (1, true), (1, true),
      (1, true), (1, true), (1, true)],
    [(0, true), (1, true), (1, true), (0, true), (1, false), (0, true), (0, true), (1, true),
      (0, true), (0, true), (1, true), (1, true)]]

end CFSG.Monster.Schur
