module

public import Certificates.Data.Kernel.PermCent.L216Twin

public section

namespace CFSG.Certificates.Kernel.PkCV.L216S

open CFSG.GH74.Uniqueness.SU.K.R4.L216M

@[expose] noncomputable def wordC (w : List Nat) : CV 17 :=
  w.foldr (fun i acc => (if i = 0 then cOf pa else cOf pb) * acc) 1

@[expose] noncomputable def sC : CV 17 := cOf sg

@[expose] noncomputable def tC : CV 17 :=
  wordC [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1]

@[expose] noncomputable def s3C : CV 17 := sC * sC * sC

@[expose] noncomputable def a1C : CV 17 := sC * tC * s3C

@[expose] noncomputable def a2C : CV 17 := sC * a1C * s3C

@[expose] noncomputable def a3C : CV 17 := sC * a2C * s3C

@[expose] noncomputable def facC : List (List (CV 17)) :=
  [[1, tC], [1, a1C], [1, a2C], [1, a3C], [1, sC, sC * sC, sC * sC * sC]]

@[expose] noncomputable def elT : List (CV 17) := productsC facC

@[expose] def conjW : List (List Nat) :=
  [[], [1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0], [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1],
    [1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0], [1, 0, 1, 0, 1], [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1],
    [1, 0, 1, 1, 0, 1, 0], [1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0], [1, 0, 1, 0, 1, 1, 0],
    [1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1], [1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1],
    [1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0], [1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1],
    [1, 0, 1, 0, 1, 0, 1, 1], [1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0],
    [1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1], [1, 0, 1, 0, 1, 1, 0, 1, 0],
    [1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0], [1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0]]

@[expose] noncomputable def conjC : List (CV 17) := conjW.map wordC

@[expose] noncomputable def nodupC (L : List (CV 17)) : Bool :=
  L.rec true fun a l r => (l.all fun b => !decide (a = b)) && r

@[expose] noncomputable def stableC (L : List (CV 17)) : Bool :=
  (L.any fun y => decide (y = 1)) &&
    L.all fun x => (L.any fun y => decide (x * tC = y)) && L.any fun y => decide (x * sC = y)

@[expose] noncomputable def covC (L C : List (CV 17)) : Bool :=
  L.all fun x => !decide (x * x = 1) || decide (x = 1) ||
    C.any fun g => eq22C g x (cOf pa) g || eq22C g x (sC * sC) g

end CFSG.Certificates.Kernel.PkCV.L216S

end
