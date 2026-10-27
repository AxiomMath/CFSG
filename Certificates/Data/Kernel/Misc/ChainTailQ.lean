module

public import Certificates.Data.Kernel.Misc.ChainTail

public section

namespace CFSG.KC.Misc.ChainTail

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def cptK (w m X p q z : Nat) : Bool :=
  Nat.beq (pg w m p (pg w m q (pg w m X z))) (pg w m X (pg w m p (pg w m q z)))

@[expose] noncomputable def ptailQ (n w : Nat) (LR TR : Nat → Nat) (X z1 z2 NE : Nat)
    (EP : Nat → Nat) : Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool)
    (fun i acc => strictB (LR i) fun R => allN (rcnt R) fun k =>
      strictB (TR (Nat.add (roff n (Nat.mul n w) R) k)) fun t =>
        Bool.rec (motive := fun _ => Bool) true
          (Bool.rec (motive := fun _ => Bool) true
            (strictB (pcomp n w (mask w) acc t) fun P =>
              !(Nat.beq (pcomp n w (mask w) P X) (pcomp n w (mask w) X P)) ||
                CFSG.KC.LQT.P.anyN NE fun e => Nat.beq P (EP e))
            (cptK w (mask w) X acc t z2))
          (cptK w (mask w) X acc t z1))
    (fun _ ih i acc => strictB (LR i) fun R => allN (rcnt R) fun k =>
      strictB (pcomp n w (mask w) acc (TR (Nat.add (roff n (Nat.mul n w) R) k))) (ih (Nat.succ i)))

end CFSG.KC.Misc.ChainTail

end
