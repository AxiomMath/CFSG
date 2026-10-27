module

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering2119S

structure V4C where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
deriving DecidableEq

structure M4C where
  m00 : Nat
  m01 : Nat
  m02 : Nat
  m03 : Nat
  m10 : Nat
  m11 : Nat
  m12 : Nat
  m13 : Nat
  m20 : Nat
  m21 : Nat
  m22 : Nat
  m23 : Nat
  m30 : Nat
  m31 : Nat
  m32 : Nat
  m33 : Nat
deriving DecidableEq

@[expose] def M4C.one : M4C :=
  ⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩

@[expose] def M4C.mul (A B : M4C) : M4C where
  m00 := (A.m00 * B.m00 + A.m01 * B.m10 + A.m02 * B.m20 + A.m03 * B.m30) % 3
  m01 := (A.m00 * B.m01 + A.m01 * B.m11 + A.m02 * B.m21 + A.m03 * B.m31) % 3
  m02 := (A.m00 * B.m02 + A.m01 * B.m12 + A.m02 * B.m22 + A.m03 * B.m32) % 3
  m03 := (A.m00 * B.m03 + A.m01 * B.m13 + A.m02 * B.m23 + A.m03 * B.m33) % 3
  m10 := (A.m10 * B.m00 + A.m11 * B.m10 + A.m12 * B.m20 + A.m13 * B.m30) % 3
  m11 := (A.m10 * B.m01 + A.m11 * B.m11 + A.m12 * B.m21 + A.m13 * B.m31) % 3
  m12 := (A.m10 * B.m02 + A.m11 * B.m12 + A.m12 * B.m22 + A.m13 * B.m32) % 3
  m13 := (A.m10 * B.m03 + A.m11 * B.m13 + A.m12 * B.m23 + A.m13 * B.m33) % 3
  m20 := (A.m20 * B.m00 + A.m21 * B.m10 + A.m22 * B.m20 + A.m23 * B.m30) % 3
  m21 := (A.m20 * B.m01 + A.m21 * B.m11 + A.m22 * B.m21 + A.m23 * B.m31) % 3
  m22 := (A.m20 * B.m02 + A.m21 * B.m12 + A.m22 * B.m22 + A.m23 * B.m32) % 3
  m23 := (A.m20 * B.m03 + A.m21 * B.m13 + A.m22 * B.m23 + A.m23 * B.m33) % 3
  m30 := (A.m30 * B.m00 + A.m31 * B.m10 + A.m32 * B.m20 + A.m33 * B.m30) % 3
  m31 := (A.m30 * B.m01 + A.m31 * B.m11 + A.m32 * B.m21 + A.m33 * B.m31) % 3
  m32 := (A.m30 * B.m02 + A.m31 * B.m12 + A.m32 * B.m22 + A.m33 * B.m32) % 3
  m33 := (A.m30 * B.m03 + A.m31 * B.m13 + A.m32 * B.m23 + A.m33 * B.m33) % 3

@[expose] def M4C.mv (A : M4C) (v : V4C) : V4C :=
  ⟨(A.m00 * v.a + A.m01 * v.b + A.m02 * v.c + A.m03 * v.d) % 3,
    (A.m10 * v.a + A.m11 * v.b + A.m12 * v.c + A.m13 * v.d) % 3,
    (A.m20 * v.a + A.m21 * v.b + A.m22 * v.c + A.m23 * v.d) % 3,
    (A.m30 * v.a + A.m31 * v.b + A.m32 * v.c + A.m33 * v.d) % 3⟩

@[expose] def V4C.om (x y : V4C) : Nat :=
  (x.a * y.c + 2 * (x.c * y.a) + x.b * y.d + 2 * (x.d * y.b)) % 3

@[expose] def V4C.add (x y : V4C) : V4C :=
  ⟨(x.a + y.a) % 3, (x.b + y.b) % 3, (x.c + y.c) % 3, (x.d + y.d) % 3⟩

@[expose] def V4C.smul (k : Nat) (x : V4C) : V4C :=
  ⟨(k * x.a) % 3, (k * x.b) % 3, (k * x.c) % 3, (k * x.d) % 3⟩

@[expose] def V4C.neg (x : V4C) : V4C := x.smul 2

@[expose] def M4C.ofCols (x0 x1 x2 x3 : V4C) : M4C :=
  ⟨x0.a, x1.a, x2.a, x3.a, x0.b, x1.b, x2.b, x3.b, x0.c, x1.c, x2.c, x3.c, x0.d, x1.d, x2.d, x3.d⟩

@[expose] def allVecs : List V4C :=
  (List.range 3).flatMap fun a => (List.range 3).flatMap fun b =>
    (List.range 3).flatMap fun c => (List.range 3).map fun d => ⟨a, b, c, d⟩

@[expose] def sympMats (μ : Nat) : List M4C :=
  allVecs.flatMap fun x0 =>
    (allVecs.filter fun x2 => x0.om x2 == μ).flatMap fun x2 =>
      (allVecs.filter fun x1 => x0.om x1 == 0 && x1.om x2 == 0).flatMap fun x1 =>
        (allVecs.filter fun x3 => x0.om x3 == 0 && x1.om x3 == μ && x2.om x3 == 0).map fun x3 =>
          M4C.ofCols x0 x1 x2 x3

@[expose] def lineC (L : Nat) : V4C :=
  match L with
  | 0 => ⟨1, 0, 0, 0⟩
  | 1 => ⟨0, 1, 0, 0⟩
  | 2 => ⟨1, 1, 0, 0⟩
  | _ => ⟨1, 2, 0, 0⟩

@[expose] def fixedList (X : M4C) : List V4C := allVecs.filter fun v => X.mv v == v

@[expose] def hList (a : V4C) (X : M4C) : List V4C := (fixedList X).filter fun h => a.om h == 0

@[expose] def fList (a : V4C) (X : M4C) : List V4C :=
  (List.range 3).flatMap fun c => (hList a X).map fun h => (a.smul c).add h

@[expose] def badList (a : V4C) (X : M4C) : List V4C :=
  (fList a X).filter fun v => !(X.mv v == v && a.om v == 0)

@[expose] def anzList : List V4C :=
  allVecs.filter fun v => v.c == 0 && v.d == 0 && !(v.a == 0 && v.b == 0)

@[expose] def xOk (a : V4C) (X : M4C) : Bool :=
  X != M4C.one && X.mul (X.mul X) == M4C.one && anzList.all (fun v => X.mv v != v) &&
    (fList a X).all (fun v => (fList a X).contains (X.mv v))

@[expose] def tOk (a : V4C) (X T : M4C) : Bool :=
  T.mul T == M4C.one && T.mv a == a && (fixedList X).all (fun v => T.mv v == v.neg)

@[expose] def invols (_ : Unit := ()) : List M4C :=
  (sympMats 2).filter fun T => T.mul T == M4C.one

@[expose] def itemsL (L : Nat) : List (M4C × M4C) :=
  let a := lineC L
  let Ts := invols ()
  ((sympMats 1).filter (xOk a)).flatMap fun X => (Ts.filter (tOk a X)).map fun T => (X, T)

@[expose] def violates (S : List V4C) (k : M4C) : Bool :=
  k != M4C.one && k.mul (k.mul k) == M4C.one && S.any fun v => k.mv v == v

@[expose] def bfsLevel (gens : List M4C) (seen frontier : List M4C) : List M4C :=
  (frontier.flatMap fun g => gens.map fun h => g.mul h).foldl
    (fun acc k => if seen.contains k || acc.contains k then acc else k :: acc) []

@[expose] def closureViol (gens : List M4C) (S : List V4C) : Nat → List M4C → List M4C → Bool
  | 0, _, _ => false
  | n + 1, seen, frontier =>
    let new := bfsLevel gens seen frontier
    new.any (violates S) || (!new.isEmpty && closureViol gens S n (seen ++ new) new)

@[expose] def pairViol (i j : Nat) (r s : M4C × M4C) : Bool :=
  closureViol [r.1, r.1.mul r.1, r.2, s.1, s.1.mul s.1, s.2]
    (anzList ++ badList (lineC i) r.1 ++ badList (lineC j) s.1) 20 [M4C.one] [M4C.one]

@[expose] def sameCyc (A B : M4C) : Bool := B == A || B == A.mul A

@[expose] def conclC (X0 X1 X2 X3 : M4C) : Bool :=
  allVecs.all (fun v => ((X1.mv v == v) == (X0.mv v == v)) && ((X2.mv v == v) == (X0.mv v == v)) &&
    ((X3.mv v == v) == (X0.mv v == v))) &&
  ((sameCyc X0 X1 && sameCyc X2 X3 && !sameCyc X0 X2) ||
   (sameCyc X0 X2 && sameCyc X1 X3 && !sameCyc X0 X1) ||
   (sameCyc X0 X3 && sameCyc X1 X2 && !sameCyc X0 X1))

@[expose] def uC (a b c : Nat) : M4C := ⟨1, 0, a, b, 0, 1, b, c, 0, 0, 1, 0, 0, 0, 0, 1⟩

@[expose] def normMats : List (M4C × M4C) :=
  (List.range 3).flatMap fun a => (List.range 3).flatMap fun b => (List.range 3).map fun c =>
    (uC a b c, uC ((3 - a) % 3) ((3 - b) % 3) ((3 - c) % 3))

@[expose] def conjC (p : M4C × M4C) (X : M4C) : M4C := p.1.mul (X.mul p.2)

@[expose] def normOK (r : M4C × M4C) : Bool :=
  r.1.mv ⟨0, 0, 1, 0⟩ == ⟨0, 0, 1, 0⟩ && r.1.mv ⟨0, 0, 0, 1⟩ == ⟨0, 0, 0, 1⟩

@[expose] def shareKCheck (_ : Unit := ()) : Bool :=
  let I0 := itemsL 0
  let I1 := itemsL 1
  let I2 := itemsL 2
  let I3 := itemsL 3
  let I0N := I0.filter normOK
  (I0.all fun r => normMats.any fun p => I0N.contains (conjC p r.1, conjC p r.2)) &&
  I0N.all fun r0 =>
    let s1 := I1.filter fun r => !pairViol 0 1 r0 r
    let s2 := I2.filter fun r => !pairViol 0 2 r0 r
    let s3 := I3.filter fun r => !pairViol 0 3 r0 r
    s1.all fun r1 => (s2.filter fun r2 => !pairViol 1 2 r1 r2).all fun r2 =>
      ((s3.filter fun r3 => !pairViol 1 3 r1 r3).filter fun r3 => !pairViol 2 3 r2 r3).all
        fun r3 => conclC r0.1 r1.1 r2.1 r3.1

end CFSG.RankThree.PartTwo.Sec21.Hering2119S
