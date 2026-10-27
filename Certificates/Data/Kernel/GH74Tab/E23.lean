module

public import Certificates.Data.Kernel.GH74Tab.E1
public import CFSG.GH74.GLS.C3.Layer2.L4ModelE2
public import CFSG.GH74.GLS.C3.Layer2.L4ModelE3

public section

namespace CFSG.KC.GH74Tab

open CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

variable (D : Dat)

@[expose] def mskL (L : List Nat) : Nat := L.foldl (fun m i => m ||| 1 <<< i) 0

@[expose] def aLK (a : Nat) : List Nat :=
  let E := eLK D a
  r64.filter fun i => E.all fun j => mul D i j == mul D j i

@[expose] def bLK (a : Nat) : List Nat :=
  let X := reachK D a 12 (1 <<< D.x0)
  let E := eLK D a
  let A := mskL (aLK D a)
  r64.filter fun i => bit D.IV i && bit A i && bit X i && !E.contains i

@[expose] def prodK (B : List Nat) (m : Nat) : Nat :=
  mul D (mul D (bif m % 2 == 1 then B.getD 0 D.one else D.one)
      (bif m / 2 % 2 == 1 then B.getD 1 D.one else D.one))
    (mul D (bif m / 4 % 2 == 1 then B.getD 2 D.one else D.one)
      (bif m / 8 % 2 == 1 then B.getD 3 D.one else D.one))

@[expose] def kleinK (Am r1 r2 : Nat) : Bool :=
  let r12 := mul D r1 r2
  bit D.IV r1 && bit D.IV r2 && r12 == mul D r2 r1 && !bit Am r1 && !bit Am r2 && !bit Am r12 &&
  r64.all fun t => bit Am t || bit Am (mul D t (g6 D.I r1)) || bit Am (mul D t (g6 D.I r2)) ||
    bit Am (mul D t (g6 D.I r12))

@[expose] def stabK (a t0 r1 r2 : Nat) : Bool :=
  let r12 := mul D r1 r2
  let K := fun s => s == D.one || s == r1 || s == r2 || s == r12
  let c := fun r => mul D (mul D t0 (g6 a r)) (g6 D.I t0)
  K (c D.one) && K (c r1) && K (c r2) && K (c r12)

@[expose] def zLK : List Nat := r64.filter fun s => r64.all fun t => mul D s t == mul D t s

@[expose] def e2K1 (a : Nat) : Bool :=
  let A := aLK D a
  bit D.IV (vIK D a) && A.length == 16 && (A.all fun i => A.all fun j => mul D i j == mul D j i) &&
  A.all fun i => mul D i i == D.one

@[expose] def e2K2 (a : Nat) (ws : List Nat) : Bool :=
  let A := aLK D a
  let B := bLK D a
  B.length == 4 && ws.length == A.length && (A.zip ws).all fun p => p.2 < 16 && p.1 == prodK D B p.2

@[expose] def e2K3 (a u : Nat) (ws : List (List Nat)) : Bool :=
  let Am := mskL (aLK D a)
  (r64.filter fun t0 => mul D (mul D t0 (g6 a t0)) u == D.one) == ws.map (·.headD 0) &&
  ws.all fun w =>
    match w with
    | [t0, r1, r2] => r1 < r2 && r2 < 64 && stabK D a t0 r1 r2 && kleinK D Am r1 r2
    | _ => false

@[expose] def e2K4 (Z : List Nat) (a : Nat) : Bool :=
  Z.all fun s => !(g6 a s == s && bit D.IV s) || s == vIK D a

@[expose] def e2OK (L : List (Nat × Nat)) (W2 : List (List Nat)) (W3 : List (List (List Nat))) :
    Bool :=
  let Z := zLK D
  e1K0 D && L.length == W2.length && L.length == W3.length &&
  (L.zip (W2.zip W3)).all fun q =>
    e2K1 D q.1.1 && e2K2 D q.1.1 q.2.1 && e2K3 D q.1.1 q.1.2 q.2.2 && e2K4 D Z q.1.1

@[expose] def wOK7 (wa wc : Nat) : Bool :=
  (List.finRange 64).all fun i =>
    (mkTab 7).wActE3.get i == g6 wa i && (mkTab 7).wCommE3.get i == bit wc i

@[expose] def labs4 : List (List Nat) :=
  (List.range 4).flatMap fun p1 => (List.range 4).flatMap fun p2 =>
    (List.range 4).flatMap fun q1 => (List.range 4).filterMap fun q2 =>
      bif p1 != p2 && p1 != q1 && p1 != q2 && p2 != q1 && p2 != q2 && q1 != q2 then
        some [p1, p2, q1, q2]
      else none

@[expose] def cjK (i x : Nat) : Nat := mul D (mul D i x) (g6 D.I i)

@[expose] def quadT (B : List Nat) (it : Nat) (l : List Nat) : Bool :=
  let b := fun k => B.getD (l.getD k 0) D.one
  cjK D it (b 0) == b 1 && cjK D it (b 1) == b 0 && cjK D it (b 2) == b 2 && cjK D it (b 3) == b 3

@[expose] def quadY (B : List Nat) (iy : Nat) (l : List Nat) : Bool :=
  let b := fun k => B.getD (l.getD k 0) D.one
  cjK D iy (b 0) == b 0 && cjK D iy (b 1) == b 1 && cjK D iy (b 2) == b 3 && cjK D iy (b 3) == b 2

@[expose] def itLK (Am : Nat) : List Nat := r64.filter fun i => bit D.IV i && !bit Am i

@[expose] def e3K (wa wc a : Nat) (w : List Nat) : Bool :=
  let E := eLK D a
  let Am := mskL (aLK D a)
  let B := bLK D a
  let IL := itLK D Am
  bit D.IV (vIK D a) && E.all (bit wc) &&
  (r64.all fun i => !(bit Am i && !E.contains i) || g6 wa i == 1) &&
  B.length == 4 &&
  (IL.all fun it => g6 wa it == 0 || labs4.all fun l => !quadT D B it l ||
    IL.all fun iy => !(mul D it iy == mul D iy it) || !quadY D B iy l) &&
  match w with
  | [it, iy, p1, p2, q1, q2] =>
    it < 64 && iy < 64 && bit D.IV it && bit D.IV iy && !bit Am it && !bit Am iy &&
    mul D it iy == mul D iy it && labs4.contains [p1, p2, q1, q2] &&
    quadT D B it [p1, p2, q1, q2] && quadY D B iy [p1, p2, q1, q2]
  | _ => false

@[expose] def e3OK (L : List (Nat × Nat)) (W4 : List (List Nat)) (wa wc : Nat) : Bool :=
  e1K0 D && wOK7 wa wc && L.length == W4.length &&
  (L.zip W4).all fun q => e3K D wa wc q.1.1 q.2

end CFSG.KC.GH74Tab

end
