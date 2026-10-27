module

public import Certificates.Data.Kernel.L34K

public section

namespace CFSG.KC.L34K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw
open CFSG.KLie.CT (andB orB notB)

@[expose] noncomputable def inK (N : Nat) (A : Nat → Nat) (x : Nat) : Bool := notB (notInK N A x)

@[expose] noncomputable def clsK (n w m : Nat) (C : Nat → Nat) (N : Nat) (A B : Nat → Nat) : Bool :=
  andB (allN m fun i =>
      orB (notB (Nat.beq (pcomp n w (mask w) (C i) (C i)) (pidn n w)))
        (orB (Nat.beq (C i) (pidn n w)) (orB (inK N A (C i)) (inK N B (C i)))))
    (allN N fun a => orB (inK N B (A a)) (allN N fun b =>
      orB (inK N A (B b))
        (notB (Nat.beq (pcomp n w (mask w) (A a) (B b)) (pcomp n w (mask w) (B b) (A a))))))

end CFSG.KC.L34K

end
