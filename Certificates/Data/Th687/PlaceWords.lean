module

public import Certificates.Data.Th687.GlueWords

public section

namespace CFSG.Sporadic.Th.Recog.Place

@[expose] def vWord : Fin 2 → List (Fin 8 × Bool) :=
  ![[(3, true), (2, true), (3, true)],
    [(2, true)]]

@[expose] def hWord : Fin 5 → List (Fin 6 × Bool) :=
  ![[(5, true), (1, false), (4, true), (5, false)],
    [(3, true), (0, true), (4, true), (1, true), (0, false)],
    [(0, true), (5, false), (0, true), (4, true), (5, true), (0, false)],
    [(0, false), (5, true), (1, false), (2, true), (5, false), (5, false)],
    [(1, true), (0, false), (5, true), (1, true), (0, false), (5, true)]]

@[expose] def aHWord : List (Fin 5 × Bool) :=
  [(2, true), (3, true), (2, true), (3, false)]

@[expose] def wpWord : Fin 2 → List (Fin 6 × Bool) :=
  ![[(0, true), (1, true), (2, true), (5, true), (0, true), (5, true), (4, true)],
    [(1, false), (5, false), (0, false), (5, true), (0, true), (4, true), (5, true)]]

@[expose] def orbWord : Fin 2 → Fin 18 → List (Fin 5 × Bool) :=
  ![![[],
      [(0, true)],
      [(1, true)],
      [(3, true)],
      [(4, false)],
      [(0, true), (1, true)],
      [(0, true), (3, true)],
      [(0, true), (4, false)],
      [(1, true), (0, true)],
      [(1, true), (3, true)],
      [(3, true), (4, false)],
      [(3, false), (0, true)],
      [(4, true), (0, true)],
      [(0, true), (1, true), (0, true)],
      [(0, true), (1, true), (3, true)],
      [(0, true), (3, false), (0, true)],
      [(1, true), (0, true), (4, false)],
      [(1, true), (4, true), (0, true)]],
    ![[],
      [(0, true)],
      [(1, true)],
      [(2, true)],
      [(3, false)],
      [(4, true)],
      [(4, false)],
      [(0, true), (1, true)],
      [(0, true), (2, true)],
      [(0, true), (3, false)],
      [(0, true), (4, true)],
      [(0, true), (4, false)],
      [(1, true), (0, true)],
      [(1, true), (4, false)],
      [(2, true), (4, false)],
      [(4, true), (2, true)],
      [(4, true), (3, false)],
      [(0, true), (2, true), (4, false)]]]

@[expose] def repWord : Fin 2 → Fin 8 → List (Fin 5 × Bool) :=
  ![![[],
      [(2, true)],
      [(1, true), (3, false)],
      [(1, true), (4, true)],
      [(3, true), (4, true)],
      [(1, true), (2, true), (3, false)],
      [(1, true), (2, true), (4, true)],
      [(2, true), (3, true), (4, true)]],
    ![[],
      [(0, true), (2, true), (0, true)],
      [(1, true), (2, true), (3, false)],
      [(4, false), (2, true), (4, true)],
      [(0, true), (1, true), (4, false), (0, true)],
      [(0, true), (3, false), (4, false), (0, true)],
      [(1, true), (0, true), (3, true), (4, true)],
      [(0, true), (1, true), (2, true), (4, false), (0, true)]]]

@[expose] def good : Fin 2 → List (Fin 8) :=
  ![[5, 7],
    [2, 6]]

@[expose] def pair : Fin 2 → Fin 8 × Fin 8 :=
  ![(7, 2),
    (5, 6)]

@[expose] def xwExpr : Twist → Fin 2 → Fin 2 → List (Fin 4 × Bool)
  | .id, 0, 0 => [(0, true), (2, false), (3, true), (1, true)]
  | .id, 0, 1 => [(2, true), (3, false), (2, false)]
  | .id, 1, 0 => [(2, false), (3, true), (0, true), (2, false), (0, true)]
  | .id, 1, 1 => [(2, true), (3, false), (2, false), (1, true), (0, true)]
  | .f1, 0, 0 => [(2, false), (0, true)]
  | .f1, 0, 1 => [(3, false), (0, true), (2, true), (1, true)]
  | .f1, 1, 0 => [(2, false), (3, false), (0, true), (2, true), (0, true)]
  | .f1, 1, 1 => [(2, true), (3, true)]
  | .f3, 0, 0 => [(3, true), (2, true), (3, true), (0, true)]
  | .f3, 0, 1 => [(3, true), (2, false), (0, true), (1, true)]
  | .f3, 1, 0 => [(3, false), (0, true)]
  | .f3, 1, 1 => [(3, true), (1, true), (0, true), (2, true)]
  | .f13, 0, 0 => [(3, true), (2, false), (3, false)]
  | .f13, 0, 1 => [(0, true), (2, true)]
  | .f13, 1, 0 => [(3, true), (2, false), (1, true)]
  | .f13, 1, 1 => [(0, true), (2, false), (3, true)]

end CFSG.Sporadic.Th.Recog.Place
