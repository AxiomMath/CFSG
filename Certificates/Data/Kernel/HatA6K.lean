module

public import Certificates.Data.HatA6Embed
public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.HatA6

open CFSG.Quasithin.H13.HatE CFSG.Quasithin.H13.HatC CFSG.Quasithin.H13.HatM

@[expose] noncomputable def fldR (M k : Nat) : Nat := Nat.land (Nat.shiftRight M (Nat.mul 6 k)) 63

@[expose] noncomputable def mactR (M c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun n ih => Nat.xor ih
    (nIf(Nat.beq (Nat.land (Nat.shiftRight c n) 1) 1, fldR M n, 0))) 6

@[expose] noncomputable def pk6 (a b c d e f : Nat) : Nat :=
  Nat.lor a (Nat.lor (Nat.shiftLeft b 6) (Nat.lor (Nat.shiftLeft c 12)
    (Nat.lor (Nat.shiftLeft d 18) (Nat.lor (Nat.shiftLeft e 24) (Nat.shiftLeft f 30)))))

@[expose] noncomputable def unpackL (M : Nat) : List Nat :=
  [fldR M 0, fldR M 1, fldR M 2, fldR M 3, fldR M 4, fldR M 5]

@[expose] noncomputable def packL (m : List Nat) : Nat :=
  pk6 (m.getD 0 0) (m.getD 1 0) (m.getD 2 0) (m.getD 3 0) (m.getD 4 0) (m.getD 5 0)

@[expose] noncomputable def mmulR (A B : Nat) : Nat :=
  pk6 (mactR A (fldR B 0)) (mactR A (fldR B 1)) (mactR A (fldR B 2)) (mactR A (fldR B 3))
    (mactR A (fldR B 4)) (mactR A (fldR B 5))

@[expose] noncomputable def IDC : Nat := pk6 1 2 4 8 16 32

@[expose] noncomputable def OMC : Nat := pk6 2 3 8 12 32 48

@[expose] noncomputable def A0C : Nat := pk6 42 63 4 8 45 54

@[expose] noncomputable def powR (M n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) IDC (fun _ ih => mmulR M ih) n

@[expose] noncomputable def allR (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => bAnd(f i, ih)) n

@[expose] noncomputable def injR (M : Nat) : Bool :=
  allR 63 (fun c => bIf(Nat.beq (mactR M (Nat.succ c)) 0, false, true))

@[expose] noncomputable def inZR (X : Nat) : Bool :=
  bIf(Nat.beq X IDC, true, bIf(Nat.beq X OMC, true, Nat.beq X (mmulR OMC OMC)))

@[expose] noncomputable def invHypR (M : Nat) : Bool :=
  bAnd(Nat.beq (mactR M (fldR M 0)) 1, bAnd(Nat.beq (mmulR M M) IDC,
    bIf(Nat.beq M IDC, false, true)))

@[expose] noncomputable def genHypR (M : Nat) : Bool :=
  bAnd(Nat.beq (mactR M (mactR M (mactR M (fldR M 0)))) 1, bAnd(Nat.beq (powR M 4) IDC,
    bAnd(inZR (powR (mmulR A0C M) 5), inZR (powR (mmulR A0C (mmulR M M)) 5))))

@[expose] noncomputable def omcR (c : Nat) : Nat :=
  Nat.lor (Nat.land (Nat.shiftRight c 1) 21)
    (Nat.shiftLeft (Nat.xor (Nat.land c 21) (Nat.land (Nat.shiftRight c 1) 21)) 1)

@[expose] noncomputable def hcR (c0 c2 c4 : Nat) : Nat :=
  pk6 c0 (omcR c0) c2 (omcR c2) c4 (omcR c4)

@[expose] noncomputable def hselR (x n v : Nat) : Nat :=
  nIf(Nat.beq (Nat.land (Nat.shiftRight x n) 1) 1, v, 0)

@[expose] noncomputable def invPR (c0 c2 : Nat) : Nat :=
  Nat.xor (Nat.xor (Nat.xor (Nat.xor 0 (hselR c0 0 c0)) (hselR c0 1 (omcR c0))) (hselR c0 2 c2))
    (hselR c0 3 (omcR c2))

@[expose] noncomputable def invQR (c0 c4 : Nat) : Nat :=
  Nat.xor (hselR c0 4 c4) (hselR c0 5 (omcR c4))

@[expose] noncomputable def invSolR (c0 t : Nat) : Nat :=
  nIf(Nat.beq (Nat.land (Nat.shiftRight c0 5) 1) 0, t,
    nIf(Nat.beq (Nat.land (Nat.shiftRight c0 4) 1) 0, omcR (omcR t), omcR t))

@[expose] noncomputable def memR (x : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun y _ ih => bIf(Nat.beq y x, true, ih)) L

@[expose] noncomputable def invEntR (K A B : Nat) : Bool :=
  bAnd(Nat.beq (mmulR A B) IDC, bAnd(Nat.beq (mmulR B A) IDC,
    bAnd(Nat.beq (mmulR A OMC) (mmulR OMC A), Nat.beq (mmulR A (mmulR A0C B)) K)))

@[expose] noncomputable def crdR (v i : Nat) : Nat := Nat.land (Nat.shiftRight v (Nat.mul 2 i)) 3

@[expose] noncomputable def trKR (c0 c2 : Nat) : Nat := Nat.xor 1 (Nat.xor (crdR c0 0) (crdR c2 1))

@[expose] noncomputable def invChkR (L : List Nat) (c0 c2 c4 : Nat) : Bool :=
  bIf(invHypR (hcR c0 c2 c4), memR (hcR c0 c2 c4) L, true)

@[expose] noncomputable def invCellR (L : List Nat) (c0 c2 p : Nat) : Bool :=
  bIf(Nat.beq (Nat.shiftRight c0 4) 0,
    bIf(Nat.beq p 1, allR 16 (fun t => invChkR L c0 c2 (Nat.add t (Nat.mul 16 (trKR c0 c2)))),
      true),
    invChkR L c0 c2 (invSolR c0 (Nat.xor p 1)))

@[expose] noncomputable def invSliceR (L : List Nat) (lo len : Nat) : Bool :=
  allR len (fun i => allR 64 (fun c2 => invCellR L (Nat.add lo i) c2 (invPR (Nat.add lo i) c2)))

@[expose] noncomputable def colPR (x c0 c2 : Nat) : Nat :=
  Nat.xor (Nat.xor (Nat.xor (Nat.xor 0 (hselR x 0 c0)) (hselR x 1 (omcR c0))) (hselR x 2 c2))
    (hselR x 3 (omcR c2))

@[expose] noncomputable def hcActR (c0 c2 c4 x : Nat) : Nat := Nat.xor (colPR x c0 c2) (invQR x c4)

@[expose] noncomputable def genPreR (c0 c2 p c4 : Nat) : Nat :=
  hcActR c0 c2 c4 (hcActR c0 c2 c4 (Nat.xor p (invQR c0 c4)))

@[expose] noncomputable def genChkR (L : List Nat) (c0 c2 c4 : Nat) : Bool :=
  bIf(genHypR (hcR c0 c2 c4), memR (hcR c0 c2 c4) L, true)

@[expose] noncomputable def genPre2R (c0 c2 c4 : Nat) : Nat :=
  hcActR c0 c2 c4 (hcActR c0 c2 c4 (hcActR c0 c2 c4 (hcActR c0 c2 c4 4)))

@[expose] noncomputable def a0ActR (c0 c2 c4 x : Nat) : Nat := hcActR 42 4 45 (hcActR c0 c2 c4 x)

@[expose] noncomputable def genPre3R (c0 c2 c4 : Nat) : Nat :=
  a0ActR c0 c2 c4 (a0ActR c0 c2 c4 (a0ActR c0 c2 c4 (a0ActR c0 c2 c4 (a0ActR c0 c2 c4 1))))

@[expose] noncomputable def a0SqR (c0 c2 c4 x : Nat) : Nat :=
  hcActR 42 4 45 (hcActR c0 c2 c4 (hcActR c0 c2 c4 x))

@[expose] noncomputable def genPre5R (c0 c2 c4 : Nat) : Nat :=
  a0SqR c0 c2 c4 (a0SqR c0 c2 c4 (a0SqR c0 c2 c4 (a0SqR c0 c2 c4 (a0SqR c0 c2 c4 1))))

@[expose] noncomputable def f4sR (k v : Nat) : Nat := Nat.xor (hselR k 0 v) (hselR k 1 (omcR v))

@[expose] noncomputable def genC4R (L : List Nat) (c0 c2 p c4 : Nat) : Bool :=
  bIf(Nat.beq (genPreR c0 c2 p c4) 1,
    bIf(Nat.blt (genPre3R c0 c2 c4) 4,
      bIf(Nat.beq (genPre2R c0 c2 c4) 4,
        bIf(Nat.blt (genPre5R c0 c2 c4) 4, memR (hcR c0 c2 c4) L, true), true), true), true)

@[expose] noncomputable def e2KR (c0 c2 : Nat) : Nat :=
  Nat.xor (Nat.xor (Nat.xor (f4sR (crdR c0 0) (crdR c2 1)) (f4sR (crdR c2 0) (crdR c0 1)))
    (f4sR (crdR c0 0) (trKR c0 c2))) (f4sR (crdR c2 1) (trKR c0 c2))

@[expose] noncomputable def hatSolR (z0 z1 C s : Nat) : Nat :=
  nIf(Nat.beq z1 0, Nat.add (f4sR (f4sR z0 z0) (Nat.xor 1 C)) (Nat.mul 4 s),
    Nat.add s (Nat.mul 4 (f4sR (f4sR z1 z1) (Nat.xor (Nat.xor 1 C) (f4sR s z0)))))

@[expose] noncomputable def genCellR (L : List Nat) (c0 c2 p : Nat) : Bool :=
  bIf(Nat.beq (Nat.add (crdR c0 2) (crdR c2 2)) 0,
    allR 16 (fun t => genC4R L c0 c2 p (Nat.add t (Nat.mul 16 (trKR c0 c2)))),
    allR 4 (fun s => genC4R L c0 c2 p
      (Nat.add (hatSolR (crdR c0 2) (crdR c2 2) (e2KR c0 c2) s) (Nat.mul 16 (trKR c0 c2)))))

@[expose] noncomputable def genSliceR (L : List Nat) (lo len : Nat) : Bool :=
  allR len (fun i => allR 64 (fun c2 => genCellR L (Nat.add lo i) c2 (invPR (Nat.add lo i) c2)))

@[expose] noncomputable def gencR (j : Nat) : Nat :=
  nIf(Nat.beq j 0, pk6 4 8 16 32 21 42, nIf(Nat.beq j 1, pk6 16 32 4 8 57 30, pk6 1 3 4 12 16 48))

@[expose] noncomputable def wvalR (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) IDC (fun j _ ih => mmulR (gencR j) ih) w

@[expose] noncomputable def genEntR (e : List Nat × Nat × List Nat) : Bool :=
  match conjTab[e.2.1]? with
  | some c => Nat.beq (wvalR e.2.2) (mmulR (packL c.2.1) (mmulR (packL e.1) (packL c.1))) &&
      e.2.2.all (· < 2)
  | none => false

@[expose] noncomputable def conjEntR (e : List Nat × List Nat × List Nat) : Bool :=
  Nat.beq (mmulR (packL e.1) (packL e.2.1)) IDC && Nat.beq (mmulR (packL e.2.1) (packL e.1)) IDC &&
    Nat.beq (wvalR e.2.2) (mmulR (packL e.2.1) (mmulR A0C (packL e.1))) && e.2.2.all (· < 2)

@[expose] noncomputable def fld36R (B j : Nat) : Nat :=
  Nat.land (Nat.shiftRight B (Nat.mul 36 j)) 68719476735

@[expose] noncomputable def packBR (G : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun y _ ih => Nat.add y (Nat.mul 68719476736 ih)) G

@[expose] noncomputable def g0HitR (B n x j : Nat) : Bool :=
  bAnd(Nat.blt j n, Nat.beq (fld36R B j) x)

@[expose] noncomputable def mmulHR (a b c M : Nat) : Nat :=
  pk6 (hcActR a b c (fldR M 0)) (hcActR a b c (fldR M 1)) (hcActR a b c (fldR M 2))
    (hcActR a b c (fldR M 3)) (hcActR a b c (fldR M 4)) (hcActR a b c (fldR M 5))

@[expose] noncomputable def g0StepR (B n M w : Nat) : Bool :=
  bAnd(g0HitR B n (mmulHR 4 16 21 M) (Nat.land w 2047),
    bAnd(g0HitR B n (mmulHR 16 4 57 M) (Nat.land (Nat.shiftRight w 11) 2047),
    bAnd(g0HitR B n (mmulHR 21 1 4 M) (Nat.land (Nat.shiftRight w 22) 2047),
    g0HitR B n (mmulHR 27 4 1 M) (Nat.shiftRight w 33))))

@[expose] noncomputable def g0WalkR (B n : Nat) (G W : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun M _ ih W => bAnd(g0StepR B n M (W.headD 0), ih W.tail)) G W

@[expose] noncomputable def g0WR (G W : List Nat) (n : Nat) : Bool :=
  bAnd(memR IDC G, bAnd(Nat.beq G.length n, g0WalkR (packBR G) n G W))

end CFSG.KC.HatA6

end
