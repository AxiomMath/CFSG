module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KS.WordF

open CFSG.KC.Enum (pcomp)

@[expose] noncomputable def evFK (n w m idn : Nat) (LP LPI : Nat → Nat) {k : Nat}
    (wd : List (Fin k × Bool)) : Nat :=
  List.rec (motive := fun _ => Nat) idn
    (fun l _ ih => pcomp n w m (Bool.rec (motive := fun _ => Nat) (LPI l.1.val) (LP l.1.val) l.2) ih)
    wd

end CFSG.KS.WordF

end
