module

public import CFSG.Sporadic.Presentation.Co2BaseInputs
public import CFSG.Certificates.WordSubgroup

public section

namespace CFSG.Sporadic.Presentation.Co2

open CFSG.CosetTable

abbrev dW : List (List (Fin 4 × Bool)) :=
[
  [(1, true), (3, true), (0, true), (3, true), (1, true), (0, true), (1, true), (3, true),
    (1, true), (0, true), (3, true), (2, true), (0, true), (2, true), (1, true), (0, true),
    (3, true), (1, true), (2, true), (0, true), (2, true), (3, true), (0, true)],
  [(0, true), (3, true), (1, true), (0, true), (1, true), (3, true), (0, true), (3, true),
    (2, true), (0, true), (2, true), (1, true), (0, true), (1, true), (2, true), (0, true),
    (2, true), (3, true), (2, true), (1, true), (3, true), (0, true), (3, true), (1, true),
    (2, true)],
  [(1, true), (3, true), (1, true), (0, true), (1, true), (3, true), (0, true), (3, true),
    (1, true), (2, true), (0, true), (2, true), (1, true), (0, true), (3, true), (0, true),
    (1, true), (0, true), (2, true), (0, true), (2, true), (1, true), (0, true), (1, true)],
  [(0, true), (3, true), (1, true), (0, true), (1, true), (3, true), (0, true), (1, true),
    (0, true), (2, true), (0, true), (2, true), (1, true), (0, true), (3, true), (1, true),
    (2, true), (0, true), (2, true), (0, true), (1, true), (3, true)]
]

abbrev dpW : List (List (Fin 4 × Bool)) :=
[
  [(3, true), (1, true), (3, true), (1, true), (0, true), (3, true), (0, true), (1, true),
    (3, true), (1, true), (2, true), (0, true), (2, true), (3, true), (1, true), (0, true),
    (3, true), (2, true), (3, true), (0, true), (3, true), (1, true), (3, true), (2, true),
    (0, true), (3, true), (2, true)],
  [(1, true), (3, true), (0, true), (1, true), (3, true), (0, true), (3, true), (1, true),
    (0, true), (1, true), (3, true), (2, true), (0, true), (2, true), (1, true), (0, true),
    (3, true), (0, true), (1, true), (3, true), (0, true), (1, true), (2, true), (0, true),
    (2, true), (3, true), (2, true), (1, true), (3, true), (0, true), (3, true), (1, true),
    (2, true)],
  [(0, true), (1, true), (3, true), (0, true), (1, true), (3, true), (0, true), (2, true),
    (3, true), (0, true), (2, true), (0, true), (3, true), (2, true), (3, true), (2, true),
    (3, true), (0, true), (3, true), (1, true), (0, true), (3, true), (1, true), (0, true)],
  [(3, true), (1, true), (3, true), (1, true), (0, true), (3, true), (0, true), (1, true),
    (3, true), (1, true), (2, true), (0, true), (2, true), (3, true), (0, true), (1, true),
    (0, true), (3, true), (2, true), (1, true), (3, true), (0, true), (3, true), (1, true),
    (0, true), (2, true)]
]

abbrev rhoW : List (Fin 4 × Bool) :=
  [(1, true), (0, true), (3, true), (0, true), (2, true), (1, true), (3, true), (2, true)]

abbrev cent4 : List (List (Fin 4 × Bool)) :=
  (List.finRange 4).map fun i => FreeGroup.invRev n34 ++ [(i, false)] ++ n34 ++ [(i, true)]

abbrev Rhat : List (List (Fin 4 × Bool)) := shortR ++ cent4

abbrev w1 : List (Fin 4 × Bool) := substWord dW rhoW ++ FreeGroup.invRev n34

abbrev w2 : List (Fin 4 × Bool) := substWord dpW rhoW

end CFSG.Sporadic.Presentation.Co2
