module

public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KC.Co3Tw

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def f12 (P r : Nat) : Nat := fld(P, Nat.mul (nat_lit 12) r, nat_lit 4095)

@[expose] noncomputable def eqB (w m BP nb p q r s : Nat) : Bool :=
  allN nb fun t => strictB (pg w m BP t) fun b =>
    Nat.beq (pg w m p (pg w m q b)) (pg w m r (pg w m s b))

@[expose] noncomputable def idB (w m BP nb p : Nat) : Bool :=
  allN nb fun t => strictB (pg w m BP t) fun b => Nat.beq (pg w m p b) b

@[expose] noncomputable def eq1B (w m BP nb p q : Nat) : Bool :=
  allN nb fun t => strictB (pg w m BP t) fun b => Nat.beq (pg w m p b) (pg w m q b)

@[expose] noncomputable def sqB (w m BP nb p q : Nat) : Bool :=
  allN nb fun t => strictB (pg w m BP t) fun b => Nat.beq (pg w m p b) (pg w m q (pg w m q b))

@[expose] noncomputable def cubeB (w m BP nb p : Nat) : Bool :=
  allN nb fun t => strictB (pg w m BP t) fun b => Nat.beq (pg w m p (pg w m p (pg w m p b))) b

@[expose] noncomputable def crOK (w m BP nb N NR RP : Nat) (T : Nat → Nat) (lo d : Nat) : Bool :=
  strictB (Nat.land d (nat_lit 4095)) fun j => strictB (fld(d, nat_lit 12, nat_lit 4095)) fun r =>
  strictB (Nat.shiftRight d (nat_lit 24)) fun t =>
    bAnd(bAnd(Nat.ble lo j, Nat.blt j N), bAnd(bAnd(Nat.blt r NR, Nat.blt t N),
      strictB (T t) fun pt => eqB w m BP nb pt (T j) (T (f12 RP r)) pt))

@[expose] noncomputable def crChk (w m BP nb N NR RP : Nat) (T : Nat → Nat) : List Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun d _ ih lo => bAnd(crOK w m BP nb N NR RP T lo d,
      ih (Nat.succ (Nat.land d (nat_lit 4095)))))

@[expose] noncomputable def cntR (r : Nat) : List Nat → Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun d _ ih => strictN ih fun c =>
      nIf(Nat.beq (fld(d, nat_lit 12, nat_lit 4095)) r, Nat.succ c, c))

@[expose] noncomputable def lenK : List Nat → Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => strictN ih Nat.succ)

@[expose] noncomputable def conjB (w m BP nb cg tp x d : Nat) : Bool :=
  allN nb fun t => strictB (pg w m BP t) fun b =>
    Nat.beq (pg w m cg (pg w m tp (pg w m x b))) (pg w m d (pg w m cg (pg w m tp b)))

@[expose] noncomputable def prOK (n w m BP nb N NC CC : Nat) (DPk : Nat → Nat) (T : Nat → Nat)
    (x lo e : Nat) : Bool :=
  strictB (Nat.land e (nat_lit 4095)) fun j => strictB (T j) fun y =>
    bAnd(bAnd(Nat.ble lo j, Nat.blt j N), bAnd(eqB w m BP nb x y y x,
      Bool.rec (motive := fun _ => Bool)
        (bIf(idB w m BP nb y, true, bIf(eq1B w m BP nb y x, true,
          bIf(sqB w m BP nb y x, true, !(cubeB w m BP nb y)))))
        (strictB (fld(e, nat_lit 13, nat_lit 7)) fun k => strictB (fld(e, nat_lit 16, nat_lit 255)) fun c =>
         strictB (fld(e, nat_lit 24, nat_lit 4095)) fun p =>
         strictB (fld(e, nat_lit 36, nat_lit 7)) fun d1 => strictB (fld(e, nat_lit 39, nat_lit 7)) fun d2 =>
          bAnd(bAnd(Nat.blt k (nat_lit 7), bAnd(Nat.blt c NC, Nat.blt p N)),
            strictB (fld(CC, Nat.mul (Nat.mul n w) c, mask (Nat.mul n w))) fun cg =>
            strictB (T p) fun tp => strictB (DPk k) fun D =>
              bAnd(conjB w m BP nb cg tp x (fld(D, Nat.mul (Nat.mul n w) d1, mask (Nat.mul n w))),
                conjB w m BP nb cg tp y (fld(D, Nat.mul (Nat.mul n w) d2, mask (Nat.mul n w))))))
        (Nat.beq (fld(e, nat_lit 12, nat_lit 1)) (nat_lit 1))))

@[expose] noncomputable def prChk (n w m BP nb N NC CC : Nat) (DPk : Nat → Nat) (T : Nat → Nat)
    (x : Nat) : List Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun e _ ih lo => bAnd(prOK n w m BP nb N NC CC DPk T x lo e,
      ih (Nat.succ (Nat.land e (nat_lit 4095)))))

end CFSG.KC.Co3Tw

end
