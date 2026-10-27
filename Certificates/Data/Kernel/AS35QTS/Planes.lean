module

public import Certificates.Data.Kernel.F4M3B
public import CFSG.Certificates.Kernel.Common.Lce

public section

namespace CFSG.KC.AS35QTS

open CFSG.KC.F4M3B

structure V3T (α : Type) where
  l0 : α
  h0 : α
  l1 : α
  h1 : α
  l2 : α
  h2 : α

structure PL (α : Type) where
  e : α
  a : V3T α
  r0 : V3T α
  r1 : V3T α
  r2 : V3T α

variable {α β : Type}

@[expose] def entV (o : Ops α) (bd : α → (α → β) → β) (u v : V3T α) (k : α → α → β) : β :=
  bd (dl o u.l0 u.h0 v.l0 v.h0 u.l1 u.h1 v.l1 v.h1 u.l2 u.h2 v.l2 v.h2) fun l =>
    bd (dh o u.l0 u.h0 v.l0 v.h0 u.l1 u.h1 v.l1 v.h1 u.l2 u.h2 v.l2 v.h2) fun h => k l h

@[expose] def mvK (o : Ops α) (bd : α → (α → β) → β) (r0 r1 r2 v : V3T α) (k : V3T α → β) : β :=
  entV o bd r0 v fun l0 h0 => entV o bd r1 v fun l1 h1 => entV o bd r2 v fun l2 h2 =>
    k ⟨l0, h0, l1, h1, l2, h2⟩

@[expose] def rowK (o : Ops α) (bd : α → (α → β) → β) (r c0 c1 c2 : V3T α) (k : V3T α → β) : β :=
  entV o bd r c0 fun l0 h0 => entV o bd r c1 fun l1 h1 => entV o bd r c2 fun l2 h2 =>
    k ⟨l0, h0, l1, h1, l2, h2⟩

@[expose] def hL (o : Ops α) (u v : V3T α) : α :=
  dl o (o.x u.l0 u.h0) u.h0 v.l0 v.h0 (o.x u.l1 u.h1) u.h1 v.l1 v.h1 (o.x u.l2 u.h2) u.h2 v.l2 v.h2

@[expose] def hH (o : Ops α) (u v : V3T α) : α :=
  dh o (o.x u.l0 u.h0) u.h0 v.l0 v.h0 (o.x u.l1 u.h1) u.h1 v.l1 v.h1 (o.x u.l2 u.h2) u.h2 v.l2 v.h2

@[expose] def col0 (X : PL α) : V3T α := ⟨X.r0.l0, X.r0.h0, X.r1.l0, X.r1.h0, X.r2.l0, X.r2.h0⟩

@[expose] def col1 (X : PL α) : V3T α := ⟨X.r0.l1, X.r0.h1, X.r1.l1, X.r1.h1, X.r2.l1, X.r2.h1⟩

@[expose] def col2 (X : PL α) : V3T α := ⟨X.r0.l2, X.r0.h2, X.r1.l2, X.r1.h2, X.r2.l2, X.r2.h2⟩

@[expose] def betaT (o : Ops α) (u w : V3T α) : α := o.x (hL o u w) (hH o u w)

@[expose] def mulK (o : Ops α) (bd : α → (α → β) → β) (X Y : PL α) (k : PL α → β) : β :=
  mvK o bd X.r0 X.r1 X.r2 Y.a fun w =>
  bd (o.x (o.x X.e Y.e) (betaT o X.a w)) fun e =>
  bd (o.x X.a.l0 w.l0) fun a0 => bd (o.x X.a.h0 w.h0) fun b0 =>
  bd (o.x X.a.l1 w.l1) fun a1 => bd (o.x X.a.h1 w.h1) fun b1 =>
  bd (o.x X.a.l2 w.l2) fun a2 => bd (o.x X.a.h2 w.h2) fun b2 =>
  rowK o bd X.r0 (col0 Y) (col1 Y) (col2 Y) fun n0 =>
  rowK o bd X.r1 (col0 Y) (col1 Y) (col2 Y) fun n1 =>
  rowK o bd X.r2 (col0 Y) (col1 Y) (col2 Y) fun n2 =>
    k ⟨e, ⟨a0, b0, a1, b1, a2, b2⟩, n0, n1, n2⟩

@[expose] def unitT (o : Ops α) (X : PL α) : α :=
  o.a (isOne o (hL o (col0 X) (col0 X)) (hH o (col0 X) (col0 X)))
  (o.a (isZero o (hL o (col0 X) (col1 X)) (hH o (col0 X) (col1 X)))
  (o.a (isZero o (hL o (col0 X) (col2 X)) (hH o (col0 X) (col2 X)))
  (o.a (isZero o (hL o (col1 X) (col0 X)) (hH o (col1 X) (col0 X)))
  (o.a (isOne o (hL o (col1 X) (col1 X)) (hH o (col1 X) (col1 X)))
  (o.a (isZero o (hL o (col1 X) (col2 X)) (hH o (col1 X) (col2 X)))
  (o.a (isZero o (hL o (col2 X) (col0 X)) (hH o (col2 X) (col0 X)))
  (o.a (isZero o (hL o (col2 X) (col1 X)) (hH o (col2 X) (col1 X)))
    (isOne o (hL o (col2 X) (col2 X)) (hH o (col2 X) (col2 X))))))))))

@[expose] def eqV (o : Ops α) (u v : V3T α) : α :=
  o.a (isEq o u.l0 u.h0 v.l0 v.h0) (o.a (isEq o u.l1 u.h1 v.l1 v.h1) (isEq o u.l2 u.h2 v.l2 v.h2))

@[expose] def eqP (o : Ops α) (X Y : PL α) : α :=
  o.a (bnot o (o.x X.e Y.e)) (o.a (eqV o X.a Y.a) (o.a (eqV o X.r0 Y.r0)
    (o.a (eqV o X.r1 Y.r1) (eqV o X.r2 Y.r2))))

@[expose] def isI3 (o : Ops α) (X : PL α) : α :=
  o.a (o.a (isOne o X.r0.l0 X.r0.h0) (o.a (isZero o X.r0.l1 X.r0.h1) (isZero o X.r0.l2 X.r0.h2)))
    (o.a (o.a (isZero o X.r1.l0 X.r1.h0) (o.a (isOne o X.r1.l1 X.r1.h1) (isZero o X.r1.l2 X.r1.h2)))
      (o.a (isZero o X.r2.l0 X.r2.h0) (o.a (isZero o X.r2.l1 X.r2.h1) (isOne o X.r2.l2 X.r2.h2))))

@[expose] def ofIx (f : Nat → α) : PL α :=
  ⟨f 24, ⟨f 22, f 23, f 20, f 21, f 18, f 19⟩, ⟨f 16, f 17, f 14, f 15, f 12, f 13⟩,
    ⟨f 10, f 11, f 8, f 9, f 6, f 7⟩, ⟨f 4, f 5, f 2, f 3, f 0, f 1⟩⟩

@[expose] def bitN (n b : Nat) : Nat := Nat.land (Nat.shiftRight n b) 1

@[expose] noncomputable def blk (w : Nat) (f : Nat → Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun i acc => Nat.add acc (Nat.shiftLeft (f i) (Nat.mul w i))) n

@[expose] noncomputable def colB (b : Nat) (G : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun g _ ih => Nat.add (bitN g b) (Nat.mul 2 ih)) G

@[expose] noncomputable def lanePl (G : List Nat) (b : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (blk 648 (fun i => Nat.mul (bitN i (Nat.sub b 18)) (Nat.sub (Nat.pow 2 648) 1)) 128)
    (blk 648 (fun _ => colB b G) 128) (Nat.blt b 18)

@[expose] def allT : Nat := Nat.sub (Nat.pow 2 82944) 1

@[expose] noncomputable def lanesK (G : List Nat) (k : PL Nat → Bool) : Bool :=
  frc (lanePl G 0) fun p0 => frc (lanePl G 1) fun p1 => frc (lanePl G 2) fun p2 =>
  frc (lanePl G 3) fun p3 => frc (lanePl G 4) fun p4 => frc (lanePl G 5) fun p5 =>
  frc (lanePl G 6) fun p6 => frc (lanePl G 7) fun p7 => frc (lanePl G 8) fun p8 =>
  frc (lanePl G 9) fun p9 => frc (lanePl G 10) fun p10 => frc (lanePl G 11) fun p11 =>
  frc (lanePl G 12) fun p12 => frc (lanePl G 13) fun p13 => frc (lanePl G 14) fun p14 =>
  frc (lanePl G 15) fun p15 => frc (lanePl G 16) fun p16 => frc (lanePl G 17) fun p17 =>
  frc (lanePl G 18) fun p18 => frc (lanePl G 19) fun p19 => frc (lanePl G 20) fun p20 =>
  frc (lanePl G 21) fun p21 => frc (lanePl G 22) fun p22 => frc (lanePl G 23) fun p23 =>
  frc (lanePl G 24) fun p24 =>
    k ⟨p24, ⟨p22, p23, p20, p21, p18, p19⟩, ⟨p16, p17, p14, p15, p12, p13⟩,
      ⟨p10, p11, p8, p9, p6, p7⟩, ⟨p4, p5, p2, p3, p0, p1⟩⟩

@[expose] def atLane (t : Nat) (X : PL Nat) (c : Nat) : PL Nat :=
  let f := fun p => Nat.mul (bitN p c) t
  ⟨f X.e, ⟨f X.a.l0, f X.a.h0, f X.a.l1, f X.a.h1, f X.a.l2, f X.a.h2⟩,
    ⟨f X.r0.l0, f X.r0.h0, f X.r0.l1, f X.r0.h1, f X.r0.l2, f X.r0.h2⟩,
    ⟨f X.r1.l0, f X.r1.h0, f X.r1.l1, f X.r1.h1, f X.r1.l2, f X.r1.h2⟩,
    ⟨f X.r2.l0, f X.r2.h0, f X.r2.l1, f X.r2.h1, f X.r2.l2, f X.r2.h2⟩⟩

@[expose] def bindP (Y : PL Nat) (k : PL Nat → Bool) : Bool :=
  frc Y.e fun e => frc Y.a.l0 fun a0 => frc Y.a.h0 fun b0 => frc Y.a.l1 fun a1 =>
  frc Y.a.h1 fun b1 => frc Y.a.l2 fun a2 => frc Y.a.h2 fun b2 =>
  frc Y.r0.l0 fun c0 => frc Y.r0.h0 fun d0 => frc Y.r0.l1 fun c1 => frc Y.r0.h1 fun d1 =>
  frc Y.r0.l2 fun c2 => frc Y.r0.h2 fun d2 =>
  frc Y.r1.l0 fun c3 => frc Y.r1.h0 fun d3 => frc Y.r1.l1 fun c4 => frc Y.r1.h1 fun d4 =>
  frc Y.r1.l2 fun c5 => frc Y.r1.h2 fun d5 =>
  frc Y.r2.l0 fun c6 => frc Y.r2.h0 fun d6 => frc Y.r2.l1 fun c7 => frc Y.r2.h1 fun d7 =>
  frc Y.r2.l2 fun c8 => frc Y.r2.h2 fun d8 =>
    k ⟨e, ⟨a0, b0, a1, b1, a2, b2⟩, ⟨c0, d0, c1, d1, c2, d2⟩, ⟨c3, d3, c4, d4, c5, d5⟩,
      ⟨c6, d6, c7, d7, c8, d8⟩⟩

@[expose] noncomputable def ind (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun c _ ih => Nat.lor (Nat.shiftLeft 1 c) ih) L

@[expose] noncomputable def incB (n : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun c _ ih lo => Bool.and' (Nat.ble lo c) (Bool.and' (Nat.blt c n) (ih (Nat.succ c)))) L 0

@[expose] noncomputable def popP (p : Nat) : Nat := CFSG.KC.popcount p 82944

@[expose] def cst (t n : Nat) : PL Nat := ofIx fun b => Nat.mul (bitN n b) t

@[expose] def ixE : Nat := 65793

@[expose] def ixT : Nat := 16843009

@[expose] noncomputable def matK (k : PL Nat → Bool) : Bool :=
  frc (pln 0 18) fun p0 => frc (pln 1 18) fun p1 => frc (pln 2 18) fun p2 =>
  frc (pln 3 18) fun p3 => frc (pln 4 18) fun p4 => frc (pln 5 18) fun p5 =>
  frc (pln 6 18) fun p6 => frc (pln 7 18) fun p7 => frc (pln 8 18) fun p8 =>
  frc (pln 9 18) fun p9 => frc (pln 10 18) fun p10 => frc (pln 11 18) fun p11 =>
  frc (pln 12 18) fun p12 => frc (pln 13 18) fun p13 => frc (pln 14 18) fun p14 =>
  frc (pln 15 18) fun p15 => frc (pln 16 18) fun p16 => frc (pln 17 18) fun p17 =>
    k ⟨0, ⟨0, 0, 0, 0, 0, 0⟩, ⟨p16, p17, p14, p15, p12, p13⟩, ⟨p10, p11, p8, p9, p6, p7⟩,
      ⟨p4, p5, p2, p3, p0, p1⟩⟩

@[expose] noncomputable def gOK (G : List Nat) : Bool :=
  Bool.and' (incB 262144 G) (frc (Nat.sub (Nat.pow 2 262144) 1) fun t =>
    matK fun X => Nat.beq (unitT (natOps t) X) (ind G))

@[expose] noncomputable def anyEq (t : Nat) (X Q : PL Nat) (S : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun s _ ih => bor (natOps t) (eqP (natOps t) Q (atLane t X s)) ih) S

@[expose] noncomputable def allHit (t : Nat) (X Q : PL Nat) (S : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun s _ ih => Bool.and' (Nat.blt 0 (eqP (natOps t) Q (atLane t X s))) ih) S

@[expose] def invM (t : Nat) (X XX : PL Nat) : Nat :=
  Nat.land (eqP (natOps t) XX (cst t ixE)) (bnot (natOps t) (eqP (natOps t) X (cst t ixE)))

@[expose] noncomputable def slOK (G S : List Nat) : Bool :=
  Bool.and' (incB 82944 S) (frc allT fun t => lanesK G fun X =>
    mulK (natOps t) frc X X fun Q => mulK (natOps t) frc Q Q fun QQ =>
      Bool.and' (Nat.beq (Nat.land (ind S) (bnot (natOps t)
          (Nat.land (invM t X Q) (bnot (natOps t) (isI3 (natOps t) X))))) 0)
        (Bool.and' (allHit t X Q S)
          (Nat.beq (Nat.land (Nat.land (invM t Q QQ) (bnot (natOps t) (isI3 (natOps t) Q)))
            (bnot (natOps t) (anyEq t X Q S))) 0)))

end CFSG.KC.AS35QTS

end
