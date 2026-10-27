module

public import Certificates.Data.Kernel.Spor.RawTree
public import CFSG.RankThree.Native.F2K
public import CFSG.Certificates.Kernel.RankThree.F2Perm
public import Std.Data.HashMap

public section

namespace CFSG.KS.MatSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.RankThree.Native.F2

@[expose] noncomputable def letM (SM SMI : Nat → Nat) (kS l : Nat) : Nat :=
  nIf(Nat.blt l kS, SM l, SMI (Nat.sub l kS))

@[expose] noncomputable def vecK (n d md PV : Nat) (LK : Nat → Nat) : Bool :=
  allN n (fun i => Nat.beq (LK (pg d md PV i)) i)

@[expose] noncomputable def bindK (n w d md L I PV P M MI : Nat) : Bool :=
  bAnd(allN n (fun i => strictB (pg w (mask w) P i) (fun y => bAnd(Nat.blt y n,
      Nat.beq (pg d md PV y) (vmulK d md (pg d md PV i) M)))),
    bAnd(Nat.beq (mulK d md L M MI) I, Nat.beq (mulK d md L MI M) I))

@[expose] noncomputable def trK (n w nw d md L I : Nat) (SM SMI TM TIM : Nat → Nat)
    (kS T R o : Nat) : Bool :=
  bAnd(Nat.beq (TM o) I, bAnd(Nat.beq (TIM o) I,
  allN (rcnt R) (fun k => bIf(Nat.beq k (nat_lit 0), true,
    strictB (stAt T (rlab n nw R k)) (fun l =>
    strictB (Nat.add o (rpar w (mask w) nw R k)) (fun q =>
    bAnd(Nat.blt l (Nat.add kS kS),
    bAnd(Nat.beq (TM (Nat.add o k)) (mulK d md L (TM q) (letM SM SMI kS l)),
      Nat.beq (TIM (Nat.add o k)) (mulK d md L (letM SMI SM kS l) (TIM q))))))))))

@[expose] noncomputable def siftMK (n w nw d md L I PV : Nat) (LK LR OF TIM : Nat → Nat)
    (BP : Nat) (f : Nat) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ G => Nat.beq G I)
    (fun _ ih l G => strictB (LR l) (fun R =>
      strictB (vmulK d md (pg d md PV (pg w (mask w) BP l)) G) (fun u =>
      strictB (LK u) (fun q => bAnd(Nat.blt q n, bAnd(Nat.beq (pg d md PV q) u,
      strictB (rpos w (mask w) nw R q) (fun k => bIf(Nat.blt k (rcnt R),
        strictB (mulK d md L G (TIM (Nat.add (OF l) k))) (ih (Nat.succ l)), false))))))))
    f

@[expose] noncomputable def schMK (n w nw d md L I PV : Nat) (PS PSI SM SMI LK LR OF TM TIM :
    Nat → Nat) (kS BP nb i T h₀ cnt : Nat) : Bool :=
  strictB T (fun T => strictB (LR i) (fun R => strictB (rcnt R) (fun c => strictB (OF i) (fun o =>
  allN cnt (fun dh => strictB (Nat.add h₀ dh) (fun h => bIf(Nat.blt h c,
    strictB (TM (Nat.add o h)) (fun th => strictB (rpt w (mask w) R h) (fun p =>
    allN (stCnt T) (fun j => strictB (stAt T j) (fun l => bAnd(Nat.blt l (Nat.add kS kS),
      strictB (rpos w (mask w) nw R (pg w (mask w) (letterK PS PSI kS l) p)) (fun k =>
      bAnd(Nat.blt k c,
        strictB (mulK d md L (mulK d md L th (letM SM SMI kS l)) (TIM (Nat.add o k)))
          (siftMK n w nw d md L I PV LK LR OF TIM BP (Nat.sub nb (Nat.succ i)) (Nat.succ i))))))))),
    true)))))))

end CFSG.KS.MatSch

end
