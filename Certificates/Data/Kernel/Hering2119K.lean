module

public import CFSG.RankThree.PartTwo.Sec21.Hering2119KData

public section

namespace CFSG.KC.H2119

open CFSG.RankThree.PartTwo.Sec21.Hering2119S

structure RowK where
  tag : Nat
  c : Nat
  v : V4C
  w : List Nat

structure ConjK where
  X : M4C
  T : M4C
  h : M4C
  h' : M4C
  m : Nat
  s1 : Nat
  s2 : Nat
  s3 : Nat
  r : Nat

@[expose] noncomputable def d4 (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) : Nat :=
  Nat.mod (Nat.add (Nat.add (Nat.add (Nat.mul a0 b0) (Nat.mul a1 b1)) (Nat.mul a2 b2))
    (Nat.mul a3 b3)) 3

@[expose] noncomputable def mulK (A B : M4C) : M4C :=
  ⟨d4 A.m00 A.m01 A.m02 A.m03 B.m00 B.m10 B.m20 B.m30,
   d4 A.m00 A.m01 A.m02 A.m03 B.m01 B.m11 B.m21 B.m31,
   d4 A.m00 A.m01 A.m02 A.m03 B.m02 B.m12 B.m22 B.m32,
   d4 A.m00 A.m01 A.m02 A.m03 B.m03 B.m13 B.m23 B.m33,
   d4 A.m10 A.m11 A.m12 A.m13 B.m00 B.m10 B.m20 B.m30,
   d4 A.m10 A.m11 A.m12 A.m13 B.m01 B.m11 B.m21 B.m31,
   d4 A.m10 A.m11 A.m12 A.m13 B.m02 B.m12 B.m22 B.m32,
   d4 A.m10 A.m11 A.m12 A.m13 B.m03 B.m13 B.m23 B.m33,
   d4 A.m20 A.m21 A.m22 A.m23 B.m00 B.m10 B.m20 B.m30,
   d4 A.m20 A.m21 A.m22 A.m23 B.m01 B.m11 B.m21 B.m31,
   d4 A.m20 A.m21 A.m22 A.m23 B.m02 B.m12 B.m22 B.m32,
   d4 A.m20 A.m21 A.m22 A.m23 B.m03 B.m13 B.m23 B.m33,
   d4 A.m30 A.m31 A.m32 A.m33 B.m00 B.m10 B.m20 B.m30,
   d4 A.m30 A.m31 A.m32 A.m33 B.m01 B.m11 B.m21 B.m31,
   d4 A.m30 A.m31 A.m32 A.m33 B.m02 B.m12 B.m22 B.m32,
   d4 A.m30 A.m31 A.m32 A.m33 B.m03 B.m13 B.m23 B.m33⟩

@[expose] noncomputable def mvK (A : M4C) (v : V4C) : V4C :=
  ⟨d4 A.m00 A.m01 A.m02 A.m03 v.a v.b v.c v.d, d4 A.m10 A.m11 A.m12 A.m13 v.a v.b v.c v.d,
   d4 A.m20 A.m21 A.m22 A.m23 v.a v.b v.c v.d, d4 A.m30 A.m31 A.m32 A.m33 v.a v.b v.c v.d⟩

@[expose] noncomputable def omK (x y : V4C) : Nat :=
  Nat.mod (Nat.add (Nat.add (Nat.add (Nat.mul x.a y.c) (Nat.mul 2 (Nat.mul x.c y.a)))
    (Nat.mul x.b y.d)) (Nat.mul 2 (Nat.mul x.d y.b))) 3

@[expose] noncomputable def addK (x y : V4C) : V4C :=
  ⟨Nat.mod (Nat.add x.a y.a) 3, Nat.mod (Nat.add x.b y.b) 3, Nat.mod (Nat.add x.c y.c) 3,
   Nat.mod (Nat.add x.d y.d) 3⟩

@[expose] noncomputable def smulK (k : Nat) (x : V4C) : V4C :=
  ⟨Nat.mod (Nat.mul k x.a) 3, Nat.mod (Nat.mul k x.b) 3, Nat.mod (Nat.mul k x.c) 3,
   Nat.mod (Nat.mul k x.d) 3⟩

@[expose] noncomputable def oneK : M4C := ⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩

@[expose] noncomputable def eqV (x y : V4C) : Bool :=
  Nat.beq x.a y.a && Nat.beq x.b y.b && Nat.beq x.c y.c && Nat.beq x.d y.d

@[expose] noncomputable def eqM (A B : M4C) : Bool :=
  Nat.beq A.m00 B.m00 && Nat.beq A.m01 B.m01 && Nat.beq A.m02 B.m02 && Nat.beq A.m03 B.m03 &&
  Nat.beq A.m10 B.m10 && Nat.beq A.m11 B.m11 && Nat.beq A.m12 B.m12 && Nat.beq A.m13 B.m13 &&
  Nat.beq A.m20 B.m20 && Nat.beq A.m21 B.m21 && Nat.beq A.m22 B.m22 && Nat.beq A.m23 B.m23 &&
  Nat.beq A.m30 B.m30 && Nat.beq A.m31 B.m31 && Nat.beq A.m32 B.m32 && Nat.beq A.m33 B.m33

@[expose] noncomputable def eqP (p q : M4C × M4C) : Bool := eqM p.1 q.1 && eqM p.2 q.2

@[expose] noncomputable def fixK (X : M4C) (v : V4C) : Bool := eqV (mvK X v) v

@[expose] noncomputable def lineK (j : Nat) : V4C :=
  Bool.rec (Bool.rec (Bool.rec ⟨1, 2, 0, 0⟩ ⟨1, 1, 0, 0⟩ (Nat.beq j 2)) ⟨0, 1, 0, 0⟩ (Nat.beq j 1))
    ⟨1, 0, 0, 0⟩ (Nat.beq j 0)

@[expose] noncomputable def all3 (f : Nat → Bool) : Bool := f 0 && f 1 && f 2

@[expose] noncomputable def allL {α : Type} (L : List α) (f : α → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => f x && ih) L

@[expose] noncomputable def isNilK {α : Type} (L : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) L

@[expose] noncomputable def memM (X : M4C) (S : List M4C) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun Y _ ih => eqM X Y || ih) S

@[expose] noncomputable def memP (p : M4C × M4C) (N : List (M4C × M4C)) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun q _ ih => eqP p q || ih) N

@[expose] noncomputable def blkXK (c0 c1 c2 : Nat) : M4C :=
  ⟨1, 0, 0, 0, 0, 1, 0, 0, c0, c1, 1, 0, c1, c2, 0, 1⟩

@[expose] noncomputable def blkTK (d0 d1 d2 : Nat) : M4C :=
  ⟨1, 0, 0, 0, 0, 1, 0, 0, d0, d1, 2, 0, d1, d2, 0, 2⟩

@[expose] noncomputable def condK (a : V4C) (c0 c1 c2 d0 d1 d2 : Nat) : Bool :=
  !Nat.beq (Nat.mod (Nat.add (Nat.mul c0 c2) (Nat.mul 2 (Nat.mul c1 c1))) 3) 0 &&
  Nat.beq (Nat.mod (Nat.add (Nat.add (Nat.mul c0 (Nat.mul a.a a.a))
    (Nat.mul 2 (Nat.mul c1 (Nat.mul a.a a.b)))) (Nat.mul c2 (Nat.mul a.b a.b))) 3) 0 &&
  Nat.beq (Nat.mod (Nat.add (Nat.mul d0 a.a) (Nat.mul d1 a.b)) 3) 0 &&
  Nat.beq (Nat.mod (Nat.add (Nat.mul d1 a.a) (Nat.mul d2 a.b)) 3) 0

@[expose] noncomputable def allNorm (a : V4C) (f : M4C × M4C → Bool) : Bool :=
  all3 fun c0 => all3 fun c1 => all3 fun c2 => all3 fun d0 => all3 fun d1 => all3 fun d2 =>
    !condK a c0 c1 c2 d0 d1 d2 || f (blkXK c0 c1 c2, blkTK d0 d1 d2)

@[expose] noncomputable def nOK (a : V4C) (N : List (M4C × M4C)) : Bool :=
  allNorm a fun p => memP p N

@[expose] noncomputable def uP (a b c : Nat) : M4C × M4C :=
  (uC a b c, uC (Nat.mod (Nat.sub 3 a) 3) (Nat.mod (Nat.sub 3 b) 3) (Nat.mod (Nat.sub 3 c) 3))

@[expose] noncomputable def conjP (u n : M4C × M4C) : M4C × M4C :=
  (mulK u.1 (mulK n.1 u.2), mulK u.1 (mulK n.2 u.2))

@[expose] noncomputable def innerL (u : M4C × M4C) (N : List (M4C × M4C))
    (k : List (M4C × M4C) → Bool) : List (M4C × M4C) → Bool :=
  List.rec (motive := fun _ => List (M4C × M4C) → Bool) k
    (fun n _ ih L => List.rec (motive := fun _ => Bool) false (fun s L' _ => eqP s (conjP u n) && ih L')
      L) N

@[expose] noncomputable def seq3 (f : Nat → (List (M4C × M4C) → Bool) → List (M4C × M4C) → Bool)
    (k : List (M4C × M4C) → Bool) : List (M4C × M4C) → Bool :=
  f 0 (f 1 (f 2 k))

@[expose] noncomputable def chkL (N L : List (M4C × M4C)) : Bool :=
  seq3 (fun a => seq3 fun b => seq3 fun c => innerL (uP a b c) N) isNilK L

@[expose] noncomputable def colK (h : M4C) (i : Nat) : V4C :=
  mvK h (Bool.rec (Bool.rec (Bool.rec ⟨0, 0, 0, 1⟩ ⟨0, 0, 1, 0⟩ (Nat.beq i 2)) ⟨0, 1, 0, 0⟩
    (Nat.beq i 1)) ⟨1, 0, 0, 0⟩ (Nat.beq i 0))

@[expose] noncomputable def simK (h : M4C) (m : Nat) : Bool :=
  Nat.beq (omK (colK h 0) (colK h 2)) m && Nat.beq (omK (colK h 1) (colK h 3)) m &&
  Nat.beq (omK (colK h 0) (colK h 1)) 0 && Nat.beq (omK (colK h 0) (colK h 3)) 0 &&
  Nat.beq (omK (colK h 1) (colK h 2)) 0 && Nat.beq (omK (colK h 2) (colK h 3)) 0

@[expose] noncomputable def lineImg (h : M4C) (i t : Nat) : Bool :=
  eqV (mvK h (lineK i)) (lineK t) || eqV (mvK h (lineK i)) (smulK 2 (lineK t))

@[expose] noncomputable def permOK (s1 s2 s3 : Nat) : Bool :=
  Nat.blt 0 s1 && Nat.blt s1 4 && Nat.blt 0 s2 && Nat.blt s2 4 && Nat.blt 0 s3 && Nat.blt s3 4 &&
  !Nat.beq s1 s2 && !Nat.beq s1 s3 && !Nat.beq s2 s3

@[expose] noncomputable def conjOK (R0 R1 : M4C × M4C) (e : ConjK) : Bool :=
  eqM (mulK e.h e.h') oneK && eqM (mulK e.h' e.h) oneK &&
  (Nat.beq e.m 1 || Nat.beq e.m 2) && simK e.h e.m && permOK e.s1 e.s2 e.s3 &&
  lineImg e.h 0 0 && lineImg e.h 1 e.s1 && lineImg e.h 2 e.s2 && lineImg e.h 3 e.s3 &&
  eqP (conjP (e.h, e.h') (e.X, e.T)) (Bool.rec R1 R0 (Nat.beq e.r 0))

@[expose] noncomputable def conjsOK (R0 R1 : M4C × M4C) (C : List ConjK) : Bool :=
  allL C (conjOK R0 R1) && allNorm (lineK 0) fun p =>
    List.rec (motive := fun _ => Bool) false (fun e _ ih => eqP p (e.X, e.T) || ih) C

@[expose] noncomputable def selK (X0 T0 X T : M4C) (l : Nat) : M4C :=
  Bool.rec (Bool.rec (Bool.rec T X (Nat.beq l 2)) T0 (Nat.beq l 1)) X0 (Nat.beq l 0)

@[expose] noncomputable def wordK (X0 T0 X T : M4C) (w : List Nat) : M4C :=
  List.rec (motive := fun _ => M4C) oneK (fun l _ ih => mulK (selK X0 T0 X T l) ih) w

@[expose] noncomputable def anzK (v : V4C) : Bool :=
  Nat.beq v.c 0 && Nat.beq v.d 0 && !(Nat.beq v.a 0 && Nat.beq v.b 0)

@[expose] noncomputable def inFHK (a : V4C) (X : M4C) (v h : V4C) : Bool :=
  fixK X h && Nat.beq (omK a h) 0 && !(fixK X v && Nat.beq (omK a v) 0)

@[expose] noncomputable def violK (X0 : M4C) (a : V4C) (X k : M4C) (r : RowK) : Bool :=
  !eqM k oneK && eqM (mulK k (mulK k k)) oneK && fixK k r.v &&
  Bool.rec (Bool.rec (inFHK a X r.v (addK r.v (smulK (Nat.mul 2 r.c) a)))
      (inFHK ⟨1, 0, 0, 0⟩ X0 r.v (addK r.v (smulK (Nat.mul 2 r.c) ⟨1, 0, 0, 0⟩)))
      (Nat.beq r.tag 1))
    (anzK r.v) (Nat.beq r.tag 0)

@[expose] noncomputable def rowK (X0 T0 : M4C) (a : V4C) (S : List M4C) (s : M4C × M4C)
    (r : RowK) : Bool :=
  Bool.rec (violK X0 a s.1 (wordK X0 T0 s.1 s.2 r.w) r) (memM s.1 S) (Nat.beq r.tag 3)

@[expose] noncomputable def rowsK (X0 T0 : M4C) (a : V4C) (S : List M4C) (L : List (M4C × M4C))
    (W : List RowK) : Bool :=
  List.rec (motive := fun _ => List RowK → Bool) isNilK
    (fun s _ ih W => List.rec (motive := fun _ => Bool) false (fun r W' _ => rowK X0 T0 a S s r && ih W')
      W) L W

@[expose] noncomputable def bEq (x y : Bool) : Bool := Bool.rec (!y) y x

@[expose] noncomputable def allV (f : V4C → Bool) : Bool :=
  all3 fun a => all3 fun b => all3 fun c => all3 fun d => f ⟨a, b, c, d⟩

@[expose] noncomputable def sameCycK (A B : M4C) : Bool := eqM B A || eqM B (mulK A A)

@[expose] noncomputable def conclR (X0 X1 X2 X3 : M4C) : Bool :=
  allV (fun v => bEq (fixK X1 v) (fixK X0 v) && bEq (fixK X2 v) (fixK X0 v) &&
    bEq (fixK X3 v) (fixK X0 v)) &&
  ((sameCycK X0 X1 && sameCycK X2 X3 && !sameCycK X0 X2) ||
   (sameCycK X0 X2 && sameCycK X1 X3 && !sameCycK X0 X1) ||
   (sameCycK X0 X3 && sameCycK X1 X2 && !sameCycK X0 X1))

@[expose] noncomputable def conclAll (X0 : M4C) (S1 S2 S3 : List M4C) : Bool :=
  allL S1 fun X1 => allL S2 fun X2 => allL S3 fun X3 => conclR X0 X1 X2 X3

end CFSG.KC.H2119
