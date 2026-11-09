module

public import Certificates.Data.Kernel.Misc.ChainTailOrb

public section

namespace CFSG.KC.Misc.ChainTail

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def ptailLK (n w : Nat) (LR TR : Nat → Nat) (BP X : Nat) (XP : Nat → Nat)
    (RL : Nat → List (Nat × Nat × Nat)) (NE : Nat) (EP : Nat → Nat) : Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool)
    (fun _ acc => !(Nat.beq (pcomp n w (mask w) acc X) (pcomp n w (mask w) X acc)) ||
      CFSG.KC.LQT.P.anyN NE fun e => Nat.beq acc (EP e))
    (fun _ ih i acc => strictB (LR i) fun R => allN (rcnt R) fun k =>
      !(relOKK w (mask w) BP XP (RL i) i acc (rpt w (mask w) R k)) ||
        ih (Nat.succ i) (pcomp n w (mask w) acc (TR (Nat.add (roff n (Nat.mul n w) R) k))))

@[expose] noncomputable def repBranchLK (n w : Nat) (LR TR : Nat → Nat) (BP X : Nat)
    (XP : Nat → Nat) (RL : Nat → List (Nat × Nat × Nat)) (NE : Nat) (EP : Nat → Nat)
    (nb q : Nat) : Bool :=
  relOKK w (mask w) BP XP (RL 0) 0 (pidn n w) (rpt w (mask w) (LR 0) q) &&
    ptailLK n w LR TR BP X XP RL NE EP (Nat.sub nb 1) 1
      (TR (Nat.add (roff n (Nat.mul n w) (LR 0)) q))

end CFSG.KC.Misc.ChainTail

end
