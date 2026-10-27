module

public import Certificates.Data.Kernel.L34Scan

public section

namespace CFSG.KC.L34Two

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin

@[expose] noncomputable def dwordK (n w : Nat) (A : Nat → Nat) (m f : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => pidn n w)
    (fun _ ih wd => strictN (Nat.land wd (nat_lit 15)) fun d =>
      nIf(Nat.beq d (nat_lit 0), pidn n w,
        pcomp n w (mask w) (A (Nat.mod (Nat.sub d (nat_lit 1)) m))
          (ih (Nat.shiftRight wd (nat_lit 4))))) f

end CFSG.KC.L34Two

end
