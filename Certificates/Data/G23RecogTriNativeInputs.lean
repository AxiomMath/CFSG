module

public import Certificates.Data.G23RecogTriInputs

public section

namespace CFSG.GH74.QTGen4.Recog.G23.P7

open CFSG.GH74.QTGen4.Recog.G23

@[expose] def triW₁ : List (Fin 6 × Bool) :=
  [(2, false), (0, false), (3, true), (2, false), (1, true), (0, false), (5, true), (1, true),
    (5, true), (1, true), (5, false), (5, false), (3, false), (5, false)]

@[expose] def triW₂ : List (Fin 6 × Bool) :=
  [(2, false), (4, false), (3, false), (1, true), (0, false), (5, true), (1, true), (5, true),
    (2, true), (5, false), (5, false), (0, false), (5, false)]

@[expose] def triE4Word : List (Fin 6 × Bool) :=
  [(2, true), (0, false), (3, true), (1, false), (0, true), (5, false), (1, false), (4, false),
    (3, false), (4, false), (1, false), (4, false), (1, false), (2, false), (5, false), (5, false),
    (3, false), (5, false), (4, false), (3, false), (1, false), (2, false), (5, false), (2, false),
    (2, false), (4, false), (5, false)]

@[expose] def triE5Word : List (Fin 6 × Bool) :=
  [(1, true), (0, false), (4, false), (1, false), (3, false), (5, false), (1, false), (3, false),
    (2, false), (4, false), (5, false), (5, false)]

@[expose] def triUWord : Fin 6 → List (Fin 6 × Bool) :=
  ![[(0, false)], [(1, false)], [(2, true)], [(3, true)], triW₁, triW₂]

@[expose] def triEWord : Fin 6 → List (Fin 6 × Bool) :=
  ![[(0, false)], [(1, false)], [(2, true)], [(3, true)], triE4Word, triE5Word]

@[expose] def substTri (r : List (Fin 6 × Bool)) : List (Fin 6 × Bool) :=
  r.flatMap fun l => if l.2 then triUWord l.1 else invWord (triUWord l.1)

end CFSG.GH74.QTGen4.Recog.G23.P7
