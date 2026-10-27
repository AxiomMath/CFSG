module

public import CFSG.Certificates.Kernel.Lie.CT.Core

public section

namespace CFSG.KC.FischerK

open CFSG.KLie.CT

@[expose] noncomputable def vecMulL (R : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun r _ ih v => Nat.xor (Bool.rec (motive := fun _ => Nat) 0 r (Nat.beq (Nat.land v 1) 1))
      (ih (Nat.shiftRight v 1))) R

@[expose] noncomputable def allIdx (p : Nat → Nat → Bool) (L : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun r _ ih i => Bool.rec (motive := fun _ => Bool) false (ih (Nat.succ i)) (p i r)) L

@[expose] noncomputable def packW (w M : Nat) (L : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun r _ ih i => Bool.rec (motive := fun _ => Bool) false (ih (Nat.succ i))
      (Nat.beq r (fget M i w))) L

end CFSG.KC.FischerK

end
