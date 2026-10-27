module

public section

namespace CFSG.KC.F4M3B

structure Ops (α : Type) where
  a : α → α → α
  x : α → α → α
  t : α
  bd : α → (α → α) → α

structure MatT (α : Type) where
  l00 : α
  h00 : α
  l01 : α
  h01 : α
  l02 : α
  h02 : α
  l10 : α
  h10 : α
  l11 : α
  h11 : α
  l12 : α
  h12 : α
  l20 : α
  h20 : α
  l21 : α
  h21 : α
  l22 : α
  h22 : α

variable {α : Type}

@[expose] def pl (o : Ops α) (a0 a1 b0 b1 : α) : α := o.x (o.a a0 b0) (o.a a1 b1)

@[expose] def ph (o : Ops α) (a0 a1 b0 b1 : α) : α := o.x (o.a (o.x a0 a1) (o.x b0 b1)) (o.a a0 b0)

@[expose] def dl (o : Ops α) (a0 a1 b0 b1 c0 c1 d0 d1 e0 e1 f0 f1 : α) : α :=
  o.x (o.x (pl o a0 a1 b0 b1) (pl o c0 c1 d0 d1)) (pl o e0 e1 f0 f1)

@[expose] def dh (o : Ops α) (a0 a1 b0 b1 c0 c1 d0 d1 e0 e1 f0 f1 : α) : α :=
  o.x (o.x (ph o a0 a1 b0 b1) (ph o c0 c1 d0 d1)) (ph o e0 e1 f0 f1)

@[expose] def ent (o : Ops α) (a0 a1 b0 b1 c0 c1 d0 d1 e0 e1 f0 f1 : α) (k : α → α → α) : α :=
  o.bd (dl o a0 a1 b0 b1 c0 c1 d0 d1 e0 e1 f0 f1) fun l =>
    o.bd (dh o a0 a1 b0 b1 c0 c1 d0 d1 e0 e1 f0 f1) fun h => k l h

@[expose] def mulK (o : Ops α) (A B : MatT α) (k : MatT α → α) : α :=
  ent o A.l00 A.h00 B.l00 B.h00 A.l01 A.h01 B.l10 B.h10 A.l02 A.h02 B.l20 B.h20 fun l00 h00 =>
  ent o A.l00 A.h00 B.l01 B.h01 A.l01 A.h01 B.l11 B.h11 A.l02 A.h02 B.l21 B.h21 fun l01 h01 =>
  ent o A.l00 A.h00 B.l02 B.h02 A.l01 A.h01 B.l12 B.h12 A.l02 A.h02 B.l22 B.h22 fun l02 h02 =>
  ent o A.l10 A.h10 B.l00 B.h00 A.l11 A.h11 B.l10 B.h10 A.l12 A.h12 B.l20 B.h20 fun l10 h10 =>
  ent o A.l10 A.h10 B.l01 B.h01 A.l11 A.h11 B.l11 B.h11 A.l12 A.h12 B.l21 B.h21 fun l11 h11 =>
  ent o A.l10 A.h10 B.l02 B.h02 A.l11 A.h11 B.l12 B.h12 A.l12 A.h12 B.l22 B.h22 fun l12 h12 =>
  ent o A.l20 A.h20 B.l00 B.h00 A.l21 A.h21 B.l10 B.h10 A.l22 A.h22 B.l20 B.h20 fun l20 h20 =>
  ent o A.l20 A.h20 B.l01 B.h01 A.l21 A.h21 B.l11 B.h11 A.l22 A.h22 B.l21 B.h21 fun l21 h21 =>
  ent o A.l20 A.h20 B.l02 B.h02 A.l21 A.h21 B.l12 B.h12 A.l22 A.h22 B.l22 B.h22 fun l22 h22 =>
  k ⟨l00, h00, l01, h01, l02, h02, l10, h10, l11, h11, l12, h12, l20, h20, l21, h21, l22, h22⟩

@[expose] def tl (o : Ops α) (a0 a1 b0 b1 c0 c1 : α) : α :=
  pl o a0 a1 (pl o b0 b1 c0 c1) (ph o b0 b1 c0 c1)

@[expose] def th (o : Ops α) (a0 a1 b0 b1 c0 c1 : α) : α :=
  ph o a0 a1 (pl o b0 b1 c0 c1) (ph o b0 b1 c0 c1)

@[expose] def detL (o : Ops α) (A : MatT α) : α :=
  o.x (o.x (o.x (tl o A.l00 A.h00 A.l11 A.h11 A.l22 A.h22) (tl o A.l01 A.h01 A.l12 A.h12 A.l20 A.h20))
      (tl o A.l02 A.h02 A.l10 A.h10 A.l21 A.h21))
    (o.x (o.x (tl o A.l02 A.h02 A.l11 A.h11 A.l20 A.h20) (tl o A.l01 A.h01 A.l10 A.h10 A.l22 A.h22))
      (tl o A.l00 A.h00 A.l12 A.h12 A.l21 A.h21))

@[expose] def detH (o : Ops α) (A : MatT α) : α :=
  o.x (o.x (o.x (th o A.l00 A.h00 A.l11 A.h11 A.l22 A.h22) (th o A.l01 A.h01 A.l12 A.h12 A.l20 A.h20))
      (th o A.l02 A.h02 A.l10 A.h10 A.l21 A.h21))
    (o.x (o.x (th o A.l02 A.h02 A.l11 A.h11 A.l20 A.h20) (th o A.l01 A.h01 A.l10 A.h10 A.l22 A.h22))
      (th o A.l00 A.h00 A.l12 A.h12 A.l21 A.h21))

@[expose] def bnot (o : Ops α) (p : α) : α := o.x p o.t

@[expose] def bor (o : Ops α) (p q : α) : α := o.x (o.x p q) (o.a p q)

@[expose] def isOne (o : Ops α) (l h : α) : α := o.a l (bnot o h)

@[expose] def isZero (o : Ops α) (l h : α) : α := o.a (bnot o l) (bnot o h)

@[expose] def isEq (o : Ops α) (l h l' h' : α) : α := o.a (bnot o (o.x l l')) (bnot o (o.x h h'))

@[expose] def scal (o : Ops α) (A : MatT α) : α :=
  o.a (isZero o A.l01 A.h01) (o.a (isZero o A.l02 A.h02) (o.a (isZero o A.l10 A.h10)
    (o.a (isZero o A.l12 A.h12) (o.a (isZero o A.l20 A.h20) (o.a (isZero o A.l21 A.h21)
      (o.a (isEq o A.l00 A.h00 A.l11 A.h11) (isEq o A.l11 A.h11 A.l22 A.h22)))))))

@[expose] def chkK (o : Ops α) (A : MatT α) : α :=
  mulK o A A fun A2 => mulK o A2 A fun A3 => mulK o A3 A2 fun A5 => mulK o A5 A5 fun A10 =>
    mulK o A10 A5 fun A15 =>
      bor o (bor o (bor o (bnot o (isOne o (detL o A) (detH o A))) (bnot o (scal o A15)))
        (scal o A5)) (scal o A3)

@[expose] def frcN (y : Nat) (k : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] def frc (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] def natOps (t : Nat) : Ops Nat := ⟨Nat.land, Nat.xor, t, frcN⟩

@[expose] noncomputable def pln (j : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat) 0 fun m ih => frcN ih fun p =>
    Nat.add p (Nat.shiftLeft
      (Nat.add p (Bool.rec (motive := fun _ => Nat) 0 (Nat.sub (Nat.pow 2 (Nat.pow 2 m)) 1)
        (Nat.beq j m))) (Nat.pow 2 m))

@[expose] noncomputable def plnK (m : Nat) (k : MatT Nat → Bool) : Bool :=
  frc (pln 0 m) fun p0 => frc (pln 1 m) fun p1 => frc (pln 2 m) fun p2 => frc (pln 3 m) fun p3 =>
  frc (pln 4 m) fun p4 => frc (pln 5 m) fun p5 => frc (pln 6 m) fun p6 => frc (pln 7 m) fun p7 =>
  frc (pln 8 m) fun p8 => frc (pln 9 m) fun p9 => frc (pln 10 m) fun p10 =>
  frc (pln 11 m) fun p11 => frc (pln 12 m) fun p12 => frc (pln 13 m) fun p13 =>
  frc (pln 14 m) fun p14 => frc (pln 15 m) fun p15 => frc (pln 16 m) fun p16 =>
  frc (pln 17 m) fun p17 =>
    k ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17⟩

@[expose] noncomputable def chkN (m : Nat) : Bool :=
  frc (Nat.sub (Nat.pow 2 (Nat.pow 2 m)) 1) fun t =>
    plnK m fun P => Nat.beq (chkK (natOps t) P) t

end CFSG.KC.F4M3B

end
