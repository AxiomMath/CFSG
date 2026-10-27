module

public import Certificates.Data.Kernel.PCent

public section

namespace CFSG.KC.PCent

open CFSG.KC.Enum (pg pcomp pidn allN)
open CFSG.KS (mask pinvS)

@[expose] noncomputable def imgMT (w g m t : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => cond (Nat.testBit m i) (Nat.lor acc (Nat.shiftLeft (nat_lit 1) (pg w (mask w) g i)))
      acc) t

@[expose] noncomputable def imgM (n w g m : Nat) : Nat := imgMT w g m n

@[expose] noncomputable def setOrbK (n w : Nat) (G : Nat → Nat) (ngen m : Nat) (R : List Rec) :
    Bool :=
  Nat.blt m (Nat.pow (nat_lit 2) n) && orbRecK (fun k y => imgM n w (G k) y) ngen m R

@[expose] noncomputable def mulRecK (n w : Nat) (G : Nat → Nat) (ngen : Nat) (R : List Rec) :
    Bool :=
  orbRecK (fun k y => pcomp n w (mask w) (G k) y) ngen (pidn n w) R

end CFSG.KC.PCent

end
