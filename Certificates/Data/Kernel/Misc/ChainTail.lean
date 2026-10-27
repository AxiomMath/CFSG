module

public import Certificates.Data.Kernel.Spor.Raw
public import Certificates.Data.Kernel.LocalQT.Perm

public section

namespace CFSG.KC.Misc.ChainTail

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def relImgK (w m BP acc i q mm : Nat) : Nat :=
  nIf(Nat.blt mm i, pg w m acc (pg w m BP mm), pg w m acc q)

@[expose] noncomputable def relOKK (w m BP : Nat) (XP : Nat → Nat) (rels : List (Nat × Nat × Nat))
    (i acc q : Nat) : Bool :=
  rels.all fun r => !(Nat.beq (Nat.max r.1 r.2.1) i) ||
    Nat.beq (relImgK w m BP acc i q r.2.1) (pg w m (XP r.2.2) (relImgK w m BP acc i q r.1))

@[expose] noncomputable def ptailK (n w : Nat) (LR TR : Nat → Nat) (BP X : Nat) (XP : Nat → Nat)
    (rels : List (Nat × Nat × Nat)) (NE : Nat) (EP : Nat → Nat) : Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool)
    (fun _ acc => !(Nat.beq (pcomp n w (mask w) acc X) (pcomp n w (mask w) X acc)) ||
      CFSG.KC.LQT.P.anyN NE fun e => Nat.beq acc (EP e))
    (fun _ ih i acc => strictB (LR i) fun R => allN (rcnt R) fun k =>
      !(relOKK w (mask w) BP XP rels i acc (rpt w (mask w) R k)) ||
        ih (Nat.succ i) (pcomp n w (mask w) acc (TR (Nat.add (roff n (Nat.mul n w) R) k))))

@[expose] noncomputable def ptailBranchK (n w : Nat) (LR TR : Nat → Nat) (BP X : Nat)
    (XP : Nat → Nat) (rels : List (Nat × Nat × Nat)) (NE : Nat) (EP : Nat → Nat) (nb k : Nat) :
    Bool :=
  !(relOKK w (mask w) BP XP rels 0 (pidn n w) (rpt w (mask w) (LR 0) k)) ||
    ptailK n w LR TR BP X XP rels NE EP (Nat.sub nb 1) 1
      (TR (Nat.add (roff n (Nat.mul n w) (LR 0)) k))

end CFSG.KC.Misc.ChainTail

end
