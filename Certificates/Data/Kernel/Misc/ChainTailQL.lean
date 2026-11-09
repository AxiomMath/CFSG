module

public import Certificates.Data.Kernel.Misc.ChainTailQ

public section

namespace CFSG.KC.Misc.ChainTail

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def ptailGK (n w : Nat) (LR TR : Nat → Nat) (BP X : Nat) (XP : Nat → Nat)
    (RL : Nat → List (Nat × Nat × Nat)) (L : Nat → Bool) : Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool)
    (fun _ acc => !(Nat.beq (pcomp n w (mask w) acc X) (pcomp n w (mask w) X acc)) || L acc)
    (fun _ ih i acc => strictB (LR i) fun R => allN (rcnt R) fun k =>
      !(relOKK w (mask w) BP XP (RL i) i acc (rpt w (mask w) R k)) ||
        ih (Nat.succ i) (pcomp n w (mask w) acc (TR (Nat.add (roff n (Nat.mul n w) R) k))))

@[expose] noncomputable def qLeafK (n w X : Nat) (L : Nat → Bool) (z1 z2 acc t : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) true
    (Bool.rec (motive := fun _ => Bool) true
      (strictB (pcomp n w (mask w) acc t) fun P =>
        !(Nat.beq (pcomp n w (mask w) P X) (pcomp n w (mask w) X P)) || L P)
      (cptK w (mask w) X acc t z2))
    (cptK w (mask w) X acc t z1)

@[expose] noncomputable def ptailQGK (n w : Nat) (LR TR : Nat → Nat) (BP X : Nat) (XP : Nat → Nat)
    (RL : Nat → List (Nat × Nat × Nat)) (L : Nat → Bool) (z1 z2 : Nat) : Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool)
    (fun i acc => strictB (LR i) fun R => allN (rcnt R) fun k =>
      !(relOKK w (mask w) BP XP (RL i) i acc (rpt w (mask w) R k)) ||
        qLeafK n w X L z1 z2 acc (TR (Nat.add (roff n (Nat.mul n w) R) k)))
    (fun _ ih i acc => strictB (LR i) fun R => allN (rcnt R) fun k =>
      !(relOKK w (mask w) BP XP (RL i) i acc (rpt w (mask w) R k)) ||
        ih (Nat.succ i) (pcomp n w (mask w) acc (TR (Nat.add (roff n (Nat.mul n w) R) k))))

@[expose] noncomputable def repBranchQK (n w : Nat) (LR TR : Nat → Nat) (BP X : Nat)
    (XP : Nat → Nat) (RL : Nat → List (Nat × Nat × Nat)) (L : Nat → Bool) (z1 z2 nb q : Nat) :
    Bool :=
  relOKK w (mask w) BP XP (RL 0) 0 (pidn n w) (rpt w (mask w) (LR 0) q) &&
    ptailQGK n w LR TR BP X XP RL L z1 z2 (Nat.sub nb 2) 1
      (TR (Nat.add (roff n (Nat.mul n w) (LR 0)) q))

end CFSG.KC.Misc.ChainTail

end
