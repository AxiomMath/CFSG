module

public import Certificates.Data.Kernel.Spor.Raw

public section

namespace CFSG.KS.CentBound

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def closK (n w m : Nat) (S SI : Nat → Nat) (kS T O x : Nat) : Bool :=
  bAnd(hasBit O x, allN n (fun p => bIf(hasBit O p,
    allN (stCnt T) (fun j => hasBit O (pg w m (letterK S SI kS (stAt T j)) p)), true)))

@[expose] noncomputable def ubCntK (n w m nw : Nat) (TRI : Nat → Nat) (R r O : Nat) : Nat :=
  strictN (rcnt R) (fun c => strictN (roff n nw R) (fun o =>
    foldUp c (fun k acc => nIf(hasBit O (pg w m (TRI (Nat.add o k)) (pg w m r (rpt w m R k))),
      Nat.succ acc, acc)) (nat_lit 0)))

@[expose] noncomputable def ubOkK (n w m : Nat) (S SI : Nat → Nat) (kS BP nb r : Nat)
    (O : Nat → Nat) : Bool :=
  allN nb (fun i => closK n w m S SI kS (stepTab kS (fixMaskK w m S kS BP (Nat.succ i))) (O i)
    (pg w m r (pg w m BP i)))

@[expose] noncomputable def ubProdK (n w m nw : Nat) (LR TRI : Nat → Nat) (nb r : Nat)
    (O : Nat → Nat) : Nat :=
  foldUp nb (fun i acc => Nat.mul acc (ubCntK n w m nw TRI (LR i) r (O i))) (nat_lit 1)

@[expose] noncomputable def tf (w m L k : Nat) : Nat := fld(L, Nat.mul w k, m)

@[expose] noncomputable def tcnt (w m L : Nat) : Nat := tf w m L (nat_lit 0)

@[expose] noncomputable def tst (w m L : Nat) : Nat := tf w m L (nat_lit 1)

@[expose] noncomputable def tpt (w m L k : Nat) : Nat :=
  tf w m L (Nat.add (nat_lit 2) (Nat.mul (nat_lit 3) k))

@[expose] noncomputable def tpar (w m L k : Nat) : Nat :=
  tf w m L (Nat.add (nat_lit 3) (Nat.mul (nat_lit 3) k))

@[expose] noncomputable def tlab (w m L k : Nat) : Nat :=
  tf w m L (Nat.add (nat_lit 4) (Nat.mul (nat_lit 3) k))

@[expose] noncomputable def tstAt (w m nh nl : Nat) (L : Nat → Nat) (t : Nat) : Nat :=
  nIf(Nat.blt t nl, tst w m (L t), nh)

@[expose] noncomputable def tmaskK (n w m L : Nat) : Nat :=
  foldUp (tcnt w m L) (fun k M => strictN (tpt w m L k) (fun p =>
    nIf(hasBit M p, Nat.lor M (Nat.shiftLeft (nat_lit 1) n), Nat.lor M (Nat.shiftLeft (nat_lit 1) p))))
    (nat_lit 0)

@[expose] noncomputable def tptK (n w m : Nat) (H : Nat → Nat) (nh s R k : Nat) : Bool :=
  strictB (tpt w m R k) (fun x => bAnd(Nat.blt x n,
    bIf(Nat.beq k (nat_lit 0), true,
      strictB (tpar w m R k) (fun pa => strictB (tlab w m R k) (fun lb =>
        bAnd(Nat.blt pa k, bAnd(Nat.ble s lb, bAnd(Nat.blt lb nh,
          Nat.beq (pg w m (H lb) (tpt w m R pa)) x))))))))

@[expose] noncomputable def tfixK (w m : Nat) (H : Nat → Nat) (nh s' x : Nat) : Bool :=
  allN (Nat.sub nh s') (fun d => Nat.beq (pg w m (H (Nat.add s' d)) x) x)

@[expose] noncomputable def tlevelK (n w m : Nat) (H L : Nat → Nat) (nh nl t : Nat) : Bool :=
  strictB (L t) (fun R => strictB (tcnt w m R) (fun c => strictB (tst w m R) (fun s =>
  strictB (tstAt w m nh nl L (Nat.succ t)) (fun s' =>
  bAnd(Nat.blt (nat_lit 0) c, bAnd(Nat.ble s s', bAnd(Nat.ble s' nh,
  bAnd(allN c (tptK n w m H nh s R),
  bAnd(bIf(hasBit (tmaskK n w m R) n, false, true),
    tfixK w m H nh s' (tpt w m R (nat_lit 0)))))))))))

@[expose] noncomputable def towerK (n w m : Nat) (H L : Nat → Nat) (nh nl : Nat) : Bool :=
  allN nl (fun t => tlevelK n w m H L nh nl t)

@[expose] noncomputable def towerProdK (w m : Nat) (L : Nat → Nat) (nl : Nat) : Nat :=
  foldUp nl (fun t acc => Nat.mul acc (tcnt w m (L t))) (nat_lit 1)

end CFSG.KS.CentBound

end
