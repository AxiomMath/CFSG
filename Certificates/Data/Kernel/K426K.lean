module

public import Certificates.Data.Kernel.B3S3K
public import Certificates.Data.Kernel.Misc.ChainTail

public section

namespace CFSG.KC.K426K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.B3S3K CFSG.KC.Misc.ChainTail

@[expose] noncomputable def bsK (T S : Nat → Nat) (x : Nat) (fuel lo hi : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun lo _ => lo)
    (fun _ ih lo hi => strictN (Nat.shiftRight (Nat.add lo hi) (nat_lit 1)) fun mid =>
      nIf(Nat.blt x (T (S mid)), ih lo mid, ih mid hi)) fuel lo hi

@[expose] noncomputable def idxK (N : Nat) (T S : Nat → Nat) (x : Nat) : Nat :=
  S (bsK T S x (nat_lit 24) (nat_lit 0) N)

@[expose] noncomputable def memIdxK (N : Nat) (T S : Nat → Nat) (x : Nat) : Bool :=
  strictB (idxK N T S x) fun j => bAnd(Nat.blt j N, Nat.beq x (T j))

@[expose] noncomputable def ptailIdxK (n w : Nat) (LR TR : Nat → Nat) (BP X : Nat) (XP : Nat → Nat)
    (rels : List (Nat × Nat × Nat)) (NE : Nat) (EP ES : Nat → Nat) : Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool)
    (fun _ acc => !(Nat.beq (pcomp n w (mask w) acc X) (pcomp n w (mask w) X acc)) ||
      memIdxK NE EP ES acc)
    (fun _ ih i acc => strictB (LR i) fun R => allN (rcnt R) fun k =>
      !(relOKK w (mask w) BP XP rels i acc (rpt w (mask w) R k)) ||
        ih (Nat.succ i) (pcomp n w (mask w) acc (TR (Nat.add (roff n (Nat.mul n w) R) k))))

@[expose] noncomputable def ptailBranchIdxK (n w : Nat) (LR TR : Nat → Nat) (BP X : Nat)
    (XP : Nat → Nat) (rels : List (Nat × Nat × Nat)) (NE : Nat) (EP ES : Nat → Nat) (nb k : Nat) :
    Bool :=
  !(relOKK w (mask w) BP XP rels 0 (pidn n w) (rpt w (mask w) (LR 0) k)) ||
    ptailIdxK n w LR TR BP X XP rels NE EP ES (Nat.sub nb 1) 1
      (TR (Nat.add (roff n (Nat.mul n w) (LR 0)) k))

@[expose] noncomputable def siftOK (n w nb : Nat) (LR TRI : Nat → Nat) (BP G : Nat) : Bool :=
  bAnd(Nat.beq (Nat.shiftRight G (Nat.mul n w)) (nat_lit 0),
    bAnd(allN n (fun i => Nat.blt (pg w (mask w) G i) n),
      siftK n w (mask w) (Nat.mul n w) (pidn n w) LR TRI BP nb (nat_lit 0) G))

@[expose] noncomputable def normalK (n w p NC NA ngC ngA : Nat) (TC SC TA SA GC GA : Nat → Nat) :
    Bool :=
  allN NA (fun k => Nat.beq (pw n w (TA k) p) (pidn n w)) &&
    allN ngA (fun l => memIdxK NC TC SC (GA l)) &&
    allN ngC (fun k => allN ngA fun l => memIdxK NA TA SA (cj n w (GC k) (GA l)))

@[expose] noncomputable def cmt (n w g h : Nat) : Nat :=
  cm n w (cm n w g h) (cm n w (pinvS n w (mask w) g) (pinvS n w (mask w) h))

@[expose] noncomputable def derivedLeK (n w ND ngC ngD : Nat) (TD SD GC GD : Nat → Nat) : Bool :=
  allN ngC (fun k => allN ngD fun l => memIdxK ND TD SD (cj n w (GC k) (GD l))) &&
    allN ngC (fun k => allN ngC fun l => memIdxK ND TD SD (cmt n w (GC k) (GC l)))

end CFSG.KC.K426K

end
