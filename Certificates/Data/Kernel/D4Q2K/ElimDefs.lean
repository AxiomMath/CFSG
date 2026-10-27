module

public import CFSG.Certificates.Kernel.Common.Loop
public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.D4Q2K

open CFSG.KC.Enum

@[expose] noncomputable def degK (x : Nat) : Nat :=
  nIf(Nat.blt x (nat_lit 2240), nat_lit 320, nat_lit 80)

@[expose] noncomputable def nbAt (l k : Nat) : Nat :=
  fld(l, Nat.mul (nat_lit 16) (Nat.succ k), nat_lit 65535)

@[expose] noncomputable def rcAt (r k : Nat) : Nat :=
  fld(r, Nat.mul (nat_lit 32) (Nat.succ k), nat_lit 4294967295)

@[expose] noncomputable def rkOf (c : Nat) : Nat := Nat.land c (nat_lit 4095)

@[expose] noncomputable def apOf (c : Nat) : Nat := fld(c, nat_lit 12, nat_lit 511)

@[expose] noncomputable def bpOf (c : Nat) : Nat := fld(c, nat_lit 21, nat_lit 511)

@[expose] noncomputable def trAt (T x : Nat) : Nat :=
  fld(T, Nat.mul (nat_lit 32) x, nat_lit 4294967295)

@[expose] noncomputable def parOf (t : Nat) : Nat := Nat.land t (nat_lit 8191)

@[expose] noncomputable def depOf (t : Nat) : Nat := fld(t, nat_lit 13, nat_lit 255)

@[expose] noncomputable def pposOf (t : Nat) : Nat := fld(t, nat_lit 21, nat_lit 511)

@[expose] noncomputable def rowOf (A S M TF : Nat → Nat) (x : Nat) : Nat :=
  nIf(Nat.blt x (nat_lit 2240), Nat.lor (A x) (Nat.shiftLeft (S x) (nat_lit 2240)),
    strictN (Nat.sub x (nat_lit 2240)) fun j =>
      Nat.lor (M j) (Nat.shiftLeft (TF j) (nat_lit 2240)))

@[expose] noncomputable def walkR (l E : Nat) (n : Nat) : Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Bool) (fun _ _ acc => Nat.beq acc E)
    (fun _ ih k b acc => strictB (nbAt l k) fun y =>
      bAnd(Nat.ble b y, bAnd(Nat.blt y (nat_lit 6720),
        strictB (Nat.succ (Nat.add acc (Nat.shiftLeft (nat_lit 1) (Nat.add (nat_lit 64) y))))
          fun acc' => ih (Nat.succ k) (Nat.succ y) acc'))) n

@[expose] noncomputable def rowV (A S M TF NL : Nat → Nat) (x : Nat) : Bool :=
  strictB (NL x) fun l => strictB (degK x) fun d =>
  strictB (Nat.shiftLeft x (nat_lit 9)) fun t =>
  bAnd(Nat.beq (Nat.land l (nat_lit 65535)) x,
    walkR l (Nat.add (Nat.shiftLeft (rowOf A S M TF x) (nat_lit 64)) (Nat.add t d)) d
      (nat_lit 0) (nat_lit 0) t)

@[expose] noncomputable def listK (NL RC : Nat → Nat) (T x l r d k : Nat) : Bool :=
  strictB (rcAt r k) fun c => strictB (rkOf c) fun rr => strictB (nbAt l k) fun y =>
  bIf(Nat.beq rr (nat_lit 0),
    bIf(bAnd(Nat.blt (nat_lit 0) y, Nat.beq (parOf (trAt T y)) x), true,
      bAnd(Nat.blt (nat_lit 0) x, Nat.beq (parOf (trAt T x)) y)),
    strictB (apOf c) fun a => strictB (bpOf c) fun b => strictB (nbAt l a) fun z =>
    bAnd(Nat.blt a d, bAnd(Nat.blt z (nat_lit 6720),
    bAnd(Bool.not (Nat.beq x z), bAnd(Bool.not (Nat.beq z y),
    bAnd(Nat.blt (rkOf (rcAt r a)) rr, bAnd(Nat.blt b (degK z),
    bAnd(Nat.beq (nbAt (NL z) b) y, Nat.blt (rkOf (rcAt (RC z) b)) rr))))))))

@[expose] noncomputable def treeK (T x l d : Nat) : Bool :=
  bIf(Nat.beq x (nat_lit 0), true, strictB (trAt T x) fun t => strictB (parOf t) fun p =>
    strictB (pposOf t) fun q =>
    bAnd(Nat.blt p (nat_lit 6720), bAnd(Nat.blt (depOf (trAt T p)) (depOf t),
    bAnd(Nat.blt q d, bAnd(Nat.beq (nbAt l q) p, Bool.not (Nat.beq p x))))))

@[expose] noncomputable def elimV (NL RC : Nat → Nat) (T x : Nat) : Bool :=
  strictB (NL x) fun l => strictB (RC x) fun r => strictB (degK x) fun d =>
  bAnd(treeK T x l d, allBlk (nat_lit 0) (listK NL RC T x l r d) d)

end CFSG.KC.D4Q2K

end
