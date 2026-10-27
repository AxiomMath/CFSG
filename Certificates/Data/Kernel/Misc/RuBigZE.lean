module

public import Certificates.Data.Kernel.Misc.RuBigZ

public section

namespace CFSG.KC.Misc.RuBigZ

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.RuInv CFSG.KC.Misc.RuScan

@[expose] noncomputable def rkX (X : Nat) : Nat :=
  nIf(Nat.beq X (nat_lit 0), nat_lit 3, nIf(Nat.beq X (nat_lit 1), nat_lit 6,
    nIf(Nat.beq X (nat_lit 2), nat_lit 3, nIf(Nat.beq X (nat_lit 3), nat_lit 4, nat_lit 5))))

@[expose] noncomputable def mAp (P : Nat → Nat) (o r m x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) x (fun i ih => strictN ih (fun y =>
    nIf(Nat.beq (fld(m, i, nat_lit 1)) (nat_lit 1), apP (P (Nat.add o i)) y, y))) r

@[expose] noncomputable def xAp (x j y : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) y (fun _ ih => strictN ih (fun v => apP x v)) j

@[expose] noncomputable def twoB (ys : List Nat) (e b : Nat) : Bool :=
  Nat.beq (yPow ys (Nat.shiftLeft (nat_lit 1) e) b) b

@[expose] noncomputable def spB (ys : List Nat) (P : Nat → Nat) (o r m : Nat) : Bool :=
  bAnd(Nat.blt m (Nat.shiftLeft (nat_lit 1) r),
    allN (nat_lit 4) (fun b => Nat.beq (yAp ys b) (mAp P o r m b)))

@[expose] noncomputable def orbOK (ys : List Nat) (x xi J : Nat) (P : Nat → Nat) (o sub pl : Nat) :
    Bool :=
  bIf(Nat.beq sub (nat_lit 0),
    strictB (fld(pl, nat_lit 0, nat_lit 4095)) (fun p =>
      bAnd(Nat.blt p (nat_lit 4060), bIf(Nat.beq (yAp ys (yAp ys p)) p, false, true))),
  bIf(Nat.beq sub (nat_lit 1),
    strictB (fld(pl, nat_lit 0, nat_lit 3)) (fun j =>
    strictB (fld(pl, nat_lit 2, nat_lit 4095)) (fun p =>
      bAnd(Nat.ble (nat_lit 1) j, bAnd(Nat.ble j J, bAnd(Nat.blt p (nat_lit 4060),
        strictB (xAp x j (yAp ys (xAp xi j p))) (fun hp =>
        strictB (yAp ys p) (fun gp =>
          bIf(Nat.beq (yAp ys hp) (xAp x j (yAp ys (xAp xi j gp))), false, true)))))))),
  bIf(Nat.beq sub (nat_lit 2), spB ys P o (nat_lit 5) pl, false)))

@[expose] noncomputable def g16B (ys : List Nat) (R : Nat → Nat) (g gi : Nat) : Bool :=
  allN (nat_lit 4) (fun k => strictB (R (Nat.add (nat_lit 12) k)) (fun v =>
    allN (nat_lit 4) (fun b =>
      Nat.beq (apP g (yAp ys (apP gi (apP v b)))) (apP v (apP g (yAp ys (apP gi b)))))))

@[expose] noncomputable def elOne (ys : List Nat) (R Q : Nat → Nat) (X rec : Nat) : Bool :=
  strictB (Nat.land rec (nat_lit 3)) (fun kd =>
  bIf(Nat.beq kd (nat_lit 0),
    strictB (fld(rec, nat_lit 2, nat_lit 15)) (fun k =>
    strictB (fld(rec, nat_lit 6, nat_lit 4095)) (fun p =>
      bAnd(Nat.blt p (nat_lit 4060),
      bIf(Nat.blt X (nat_lit 5),
        bAnd(Nat.blt k (rkX X), strictB (R (Nat.add (bX X) k)) (fun v =>
          bIf(Nat.beq (yAp ys (apP v p)) (apP v (yAp ys p)), false, true))),
        bAnd(Nat.blt k (nat_lit 4),
          strictB (yAp ys (apP (R (Nat.add (nat_lit 12) k)) p)) (fun q =>
          strictB (yAp ys p) (fun gp =>
            allN (nat_lit 16) (fun w =>
              bIf(Nat.beq (apP (R (Nat.add (nat_lit 21) w)) gp) q, false, true))))))))),
  bIf(Nat.beq kd (nat_lit 1),
    bIf(Nat.beq X (nat_lit 0),
      orbOK ys (Q 10) (Q 11) (nat_lit 3) Q (nat_lit 0) (fld(rec, nat_lit 2, nat_lit 3))
        (Nat.shiftRight rec (nat_lit 4)),
    bIf(Nat.blt X (nat_lit 3), spB ys R (nat_lit 3) (nat_lit 6) (Nat.shiftRight rec (nat_lit 2)),
    bIf(Nat.blt X (nat_lit 5),
      bAnd(allN (nat_lit 4) (fun b => twoB ys (fld(rec, Nat.add (nat_lit 2) (Nat.mul (nat_lit 3) b),
          nat_lit 7)) b),
      bIf(Nat.beq X (nat_lit 3),
        bAnd(g16B ys R (Q 16) (Q 17),
          orbOK ys (Q 12) (Q 13) (nat_lit 2) Q (nat_lit 5) (fld(rec, nat_lit 14, nat_lit 3))
            (Nat.shiftRight rec (nat_lit 16))),
        orbOK ys (Q 14) (Q 15) (nat_lit 2) R (nat_lit 16) (fld(rec, nat_lit 14, nat_lit 3))
          (Nat.shiftRight rec (nat_lit 16)))),
      allN (nat_lit 4) (fun b => strictB (fld(rec, Nat.add (nat_lit 2) (Nat.mul (nat_lit 4) b),
          nat_lit 15)) (fun e => bAnd(Nat.ble e (nat_lit 10), twoB ys e b)))))),
    false)))

@[expose] noncomputable def elChk (LR TR R Q AL EL : Nat → Nat) (X lo cnt : Nat) : Bool :=
  strictB (roff (nat_lit 4060) (nat_lit 48720) (LR 0)) (fun o0 =>
  strictB (roff (nat_lit 4060) (nat_lit 48720) (LR 1)) (fun o1 =>
  strictB (roff (nat_lit 4060) (nat_lit 48720) (LR 2)) (fun o2 =>
  strictB (rcnt (LR 2)) (fun c2 =>
  strictB (Nat.mul (rcnt (LR 1)) c2) (fun n =>
  allN cnt (fun d => strictB (Nat.add lo d) (fun a =>
    strictB (AL a) (fun i =>
    bAnd(Nat.blt i (rcnt (LR 0)),
    strictB (TR (Nat.add o0 i)) (fun t0 =>
    strictB (Nat.mul n a) (fun base =>
    allN n (fun j =>
      strictB (TR (Nat.add o1 (Nat.div j c2))) (fun t1 =>
      strictB (TR (Nat.add o2 (Nat.mod j c2))) (fun t2 =>
        elOne [t0, t1, t2] R Q X (EL (Nat.add base j))))))))))))))))

@[expose] noncomputable def alChk (LR L AL : Nat → Nat) (X n : Nat) : Bool :=
  strictB (rcnt (LR 0)) (fun c0 =>
  bAnd(allN n (fun a => strictB (AL a) (fun i =>
      bAnd(Nat.blt i c0, bAnd(Nat.beq (L (Nat.add (Nat.mul (nat_lit 21) i) X)) (nat_lit 1),
        bIf(Nat.blt (Nat.succ a) n, Nat.blt i (AL (Nat.succ a)), true))))),
    Nat.beq (foldN c0 (fun i s =>
      nIf(Nat.beq (L (Nat.add (Nat.mul (nat_lit 21) i) X)) (nat_lit 1), Nat.succ s, s)) (nat_lit 0))
      n))

@[expose] noncomputable def l0kOK (L : Nat → Nat) (i : Nat) : Bool :=
  allN (nat_lit 6) (fun X => strictB (L (Nat.add (Nat.mul (nat_lit 21) i) X)) (fun rec =>
    bIf(Nat.beq rec (nat_lit 1), true,
      Nat.blt (fld(rec, nat_lit 1, nat_lit 15)) (nIf(Nat.blt X (nat_lit 5), rkX X, nat_lit 4)))))

@[expose] noncomputable def l0kChk (L : Nat → Nat) (n : Nat) : Bool := allN n (fun i => l0kOK L i)

end CFSG.KC.Misc.RuBigZ

end
