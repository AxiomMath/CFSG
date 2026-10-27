module

public import Certificates.Data.Kernel.Misc.PermClosW

public section

namespace CFSG.KC.Misc.Fuse

open CFSG.KC.Ord CFSG.KS CFSG.KC.Misc.ClosW
open CFSG.KC.Enum (pcomp pidn)
open CFSG.KC.LQT.P (letB impB)

@[expose] noncomputable def conjM (n w x g : Nat) : Nat :=
  pcomp n w (mask w) (pcomp n w (mask w) g x) (pinvS n w (mask w) g)

@[expose] noncomputable def commK (n w x y : Nat) : Bool :=
  Nat.beq (pcomp n w (mask w) x y) (pcomp n w (mask w) y x)

@[expose] noncomputable def fuseAt (n w R0 : Nat) (E : Nat → Nat) (SG : Nat → Nat) (nS : Nat)
    (SW : Nat → List Nat) (SC : Nat → Nat) (k : Nat) : Bool :=
  letB (E k) fun c => impB (andB (Nat.beq (pcomp n w (mask w) c c) (pidn n w))
    (notB (Nat.beq c (pidn n w))))
    (andB (wWordAt n w SG nS SW SC k)
      (Nat.beq (pcomp n w (mask w) (SC k) R0) (pcomp n w (mask w) (pcomp n w (mask w) R0 c) (SC k))))

end CFSG.KC.Misc.Fuse

end
