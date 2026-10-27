module

public import Certificates.Data.Kernel.Misc.ArrEnum

public section

namespace CFSG.KC.Misc.ConjWit

open CFSG.KC.Enum (pcomp)
open CFSG.KS (mask)

@[expose] noncomputable def cwE (n w h s t : Nat) : Bool :=
  Nat.beq (pcomp n w (mask w) h s) (pcomp n w (mask w) t h)

@[expose] noncomputable def witK (n w S B NH NT : Nat) (H TT : Nat → Nat) (Z0 Z1 Z2 s wit : Nat) :
    Bool :=
  Bool.rec (motive := fun _ => Bool)
    (Nat.beq s Z0 || Nat.beq s Z1 || Nat.beq s Z2)
    (Nat.blt (Nat.mod wit B) NH && Nat.blt (Nat.div wit B) NT &&
      cwE n w (H (Nat.mod wit B)) s (TT (Nat.div wit B)))
    (Nat.blt wit S)

@[expose] noncomputable def witL (n w S B NH NT : Nat) (H TT P : Nat → Nat) (Z0 Z1 Z2 : Nat)
    (W : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun wit _ ih i => witK n w S B NH NT H TT Z0 Z1 Z2 (P i) wit && ih (Nat.add i 1)) W

end CFSG.KC.Misc.ConjWit

end
