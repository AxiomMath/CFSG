module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.U43Inv

open CFSG.KC.Enum

@[expose] noncomputable def lwalk {α : Type} (f : Nat → α → Bool) (n : Nat) (L : List α) :
    Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i n)
    (fun x _ ih i => strictB i fun i => bAnd(f i x, ih (Nat.succ i))) L

@[expose] noncomputable def oOrd (κ : Nat → Nat) (n : Nat) (O : Nat → Nat) : Bool :=
  allN (Nat.sub n (nat_lit 1)) fun i => bAnd(Nat.blt (O i) n, bAnd(Nat.blt (O (Nat.succ i)) n,
    Nat.blt (κ (O i)) (κ (O (Nat.succ i)))))

@[expose] noncomputable def bNot (b : Bool) : Bool := bIf(b, false, true)

@[expose] noncomputable def kf (r t : Nat) : Nat := fld(r, Nat.mul (nat_lit 10) t, nat_lit 1023)

@[expose] noncomputable def kdep (r : Nat) : Nat := fld(r, nat_lit 30, nat_lit 255)

@[expose] noncomputable def kpar (r : Nat) : Nat := fld(r, nat_lit 38, nat_lit 2047)

@[expose] noncomputable def klab (r : Nat) : Nat := fld(r, nat_lit 49, nat_lit 15)

@[expose] noncomputable def keys3 (G : Nat → Nat) (r r' : Nat) : Bool :=
  bAnd(Nat.beq (kf r' (nat_lit 0)) (G (kf r (nat_lit 0))),
    bAnd(Nat.beq (kf r' (nat_lit 1)) (G (kf r (nat_lit 1))),
      Nat.beq (kf r' (nat_lit 2)) (G (kf r (nat_lit 2)))))

@[expose] noncomputable def kRecOK (R : Nat → Nat) (n nl : Nat) (Gk : Nat → Nat → Nat) (k : Nat) :
    Bool :=
  strictB (R k) fun r => bIf(Nat.beq k (nat_lit 0),
    bAnd(Nat.beq (kdep r) (nat_lit 0), bAnd(Nat.beq (kf r (nat_lit 0)) (nat_lit 0),
      bAnd(Nat.beq (kf r (nat_lit 1)) (nat_lit 1), Nat.beq (kf r (nat_lit 2)) (nat_lit 9)))),
    strictB (kpar r) fun p => strictB (klab r) fun l =>
      bAnd(Nat.blt p n, bAnd(Nat.blt l nl, strictB (R p) fun rp =>
        bAnd(Nat.blt (kdep rp) (kdep r), bAnd(Nat.blt (kdep r) (nat_lit 33),
          keys3 (Gk l) rp r)))))

@[expose] noncomputable def kTree (R : Nat → Nat) (n nl : Nat) (Gk : Nat → Nat → Nat) : Bool :=
  allN n (kRecOK R n nl Gk)

@[expose] noncomputable def fldsAre (R : Nat → Nat) (fa : Nat → Nat) (n : Nat) (L : List Nat) :
    Bool :=
  lwalk (fun i x => Nat.beq (fa (R i)) x) n L (nat_lit 0)

@[expose] noncomputable def kClos (R : Nat → Nat) (n nl : Nat) (Gk : Nat → Nat → Nat)
    (tbl : List Nat) : Bool :=
  lwalk (fun i x => bAnd(Nat.blt x n, keys3 (Gk (Nat.mod i nl)) (R (Nat.div i nl)) (R x)))
    (Nat.mul n nl) tbl (nat_lit 0)

@[expose] noncomputable def kkey (r : Nat) : Nat := Nat.land r (nat_lit 1073741823)

@[expose] noncomputable def kOrd (R : Nat → Nat) (n : Nat) (O : Nat → Nat) : Bool :=
  oOrd (fun x => kkey (R x)) n O

@[expose] noncomputable def eW (R : Nat → Nat) (Gr : Nat → Nat → Nat) (f : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ q => q)
    (fun _ ih k q => strictN (R k) fun r =>
      nIf(Nat.beq (kdep r) (nat_lit 0), q, ih (kpar r) (Gr (klab r) q))) f

@[expose] noncomputable def eWi (R : Nat → Nat) (Gk : Nat → Nat → Nat) (f : Nat) :
    Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ q => q)
    (fun _ ih k q => strictN (R k) fun r =>
      nIf(Nat.beq (kdep r) (nat_lit 0), q, Gk (klab r) (ih (kpar r) q))) f

@[expose] noncomputable def cf (r t : Nat) : Nat := fld(r, Nat.mul (nat_lit 10) t, nat_lit 1023)

@[expose] noncomputable def cdep (r : Nat) : Nat := fld(r, nat_lit 200, nat_lit 255)

@[expose] noncomputable def cpar (r : Nat) : Nat := fld(r, nat_lit 208, nat_lit 4095)

@[expose] noncomputable def clab (r : Nat) : Nat := fld(r, nat_lit 220, nat_lit 3)

@[expose] noncomputable def orM (f : Nat → Nat) (m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun t ih => Nat.lor (Nat.shiftLeft (nat_lit 1) (f t)) ih) m

@[expose] noncomputable def cRecOK (R : Nat → Nat) (n : Nat) (Lp : Nat → Nat → Nat) (k : Nat) :
    Bool :=
  strictB (R k) fun r => bIf(Nat.beq k (nat_lit 0), Nat.beq (cdep r) (nat_lit 0),
    strictB (cpar r) fun p => strictB (clab r) fun l =>
      bAnd(Nat.blt p n, strictB (R p) fun rp =>
        bAnd(Nat.blt (cdep rp) (cdep r), bAnd(Nat.blt (cdep r) (nat_lit 33),
          Nat.beq (orM (cf r) (nat_lit 20)) (orM (fun t => Lp l (cf rp t)) (nat_lit 20))))))

@[expose] noncomputable def cTree (R : Nat → Nat) (n : Nat) (Lp : Nat → Nat → Nat) : Bool :=
  allN n (cRecOK R n Lp)

@[expose] noncomputable def bt (m q : Nat) : Nat := Nat.land (Nat.shiftRight m q) (nat_lit 1)

@[expose] noncomputable def cFix (R : Nat → Nat) (A : Nat → Nat) : Bool :=
  strictB (orM (cf (R (nat_lit 0))) (nat_lit 20)) fun m => allN (nat_lit 1024) fun q =>
    bIf(Nat.blt q (nat_lit 820), bIf(Nat.beq (A q) q, Nat.beq (bt m q) (nat_lit 1),
      Nat.beq (bt m q) (nat_lit 0)), Nat.beq (bt m q) (nat_lit 0))

@[expose] noncomputable def cOrd (R : Nat → Nat) (n : Nat) (O : Nat → Nat) : Bool :=
  oOrd (fun x => orM (cf (R x)) (nat_lit 20)) n O

@[expose] noncomputable def mwv (Lp : Nat → Nat → Nat) (w : List Nat) (q : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun q => q) (fun l _ ih q => Lp l (ih q)) w q

@[expose] noncomputable def mwvI (Lp : Nat → Nat → Nat) (w : List Nat) (q : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun q => q)
    (fun l _ ih q => ih (Lp (Nat.xor l (nat_lit 2)) q)) w q

@[expose] noncomputable def base3 (f g : Nat → Nat) : Bool :=
  bAnd(Nat.beq (f (nat_lit 0)) (g (nat_lit 0)), bAnd(Nat.beq (f (nat_lit 1)) (g (nat_lit 1)),
    Nat.beq (f (nat_lit 9)) (g (nat_lit 9))))

@[expose] noncomputable def f2Rec (E Ei : Nat → Nat → Nat) (A : Nat → Nat) (n k x d : Nat) : Bool :=
  strictB (fld(d, nat_lit 0, nat_lit 3)) fun t => strictB (fld(d, nat_lit 2, nat_lit 1023)) fun q =>
    bIf(Nat.beq t (nat_lit 0), base3 (E k) (fun p => p),
    bIf(Nat.beq t (nat_lit 1), bAnd(Nat.blt q (nat_lit 820), bNot (Nat.beq (E k (E k q)) q)),
    bIf(Nat.beq t (nat_lit 2), base3 (E k) A,
      bAnd(Nat.blt x n, bAnd(Nat.blt q (nat_lit 820),
        bNot (Nat.beq (E k (E x (E k (Ei x q)))) (E x (E k (Ei x (E k q))))))))))

@[expose] noncomputable def f2All (E Ei : Nat → Nat → Nat) (A : Nat → Nat) (F : Nat → Nat) (n : Nat)
    (W : List Nat) : Bool :=
  lwalk (fun k x => f2Rec E Ei A n k x (F k)) n W (nat_lit 0)

@[expose] noncomputable def g0Chk (Lp : Nat → Nat → Nat) (A : Nat → Nat) (w : List Nat) (q0 : Nat) :
    Bool :=
  bAnd(Nat.blt q0 (nat_lit 820), allN (nat_lit 5) fun i => bNot (Nat.beq
    (Nat.rec (motive := fun _ => Nat) q0 (fun _ ih => A (mwv Lp w (A (mwvI Lp w ih)))) (Nat.succ i))
    q0))

end CFSG.KC.U43Inv

end
