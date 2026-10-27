module

public import Init

public section

namespace CFSG.KC.MonPcFive

structure RV where
  a0 : Nat
  a1 : Nat
  a2 : Nat
  a3 : Nat
  a4 : Nat
  a5 : Nat
  c : Nat

structure CM6 where
  m01 : Nat
  m02 : Nat
  m03 : Nat
  m04 : Nat
  m05 : Nat
  m12 : Nat
  m13 : Nat
  m14 : Nat
  m15 : Nat
  m23 : Nat
  m24 : Nat
  m25 : Nat
  m34 : Nat
  m35 : Nat
  m45 : Nat

@[expose] def RV.one : RV := ⟨0, 0, 0, 0, 0, 0, 0⟩

@[expose] def RV.xg : RV := ⟨0, 0, 0, 0, 0, 0, 1⟩

@[expose] def RV.xc (c : Nat) : RV := ⟨0, 0, 0, 0, 0, 0, c⟩

@[expose] def mulR (m : CM6) (a b : RV) : RV :=
  ⟨(a.a0 + b.a0) % 5, (a.a1 + b.a1) % 5, (a.a2 + b.a2) % 5, (a.a3 + b.a3) % 5,
    (a.a4 + b.a4) % 5, (a.a5 + b.a5) % 5,
    (a.c + b.c + a.a5 * (b.a0 * m.m05 + b.a1 * m.m15 + b.a2 * m.m25 + b.a3 * m.m35 + b.a4 * m.m45) +
      a.a4 * (b.a0 * m.m04 + b.a1 * m.m14 + b.a2 * m.m24 + b.a3 * m.m34) +
      a.a3 * (b.a0 * m.m03 + b.a1 * m.m13 + b.a2 * m.m23) + a.a2 * (b.a0 * m.m02 + b.a1 * m.m12) +
      a.a1 * (b.a0 * m.m01)) % 5⟩

@[expose] def cmM : CM6 := ⟨2, 0, 0, 0, 0, 1, 0, 3, 3, 0, 4, 3, 0, 2, 0⟩

@[expose] def powR (m : CM6) (r : RV) : Nat → RV
  | 0 => RV.one
  | k + 1 => mulR m (powR m r k) r

structure RAct where
  r0 : RV
  r1 : RV
  r2 : RV
  r3 : RV
  r4 : RV
  r5 : RV

@[expose] def applyR (m : CM6) (A : RAct) (a : RV) : RV :=
  mulR m (mulR m (mulR m (mulR m (mulR m (mulR m (powR m A.r0 a.a0) (powR m A.r1 a.a1))
    (powR m A.r2 a.a2)) (powR m A.r3 a.a3)) (powR m A.r4 a.a4)) (powR m A.r5 a.a5))
    (powR m RV.xg a.c)

structure RP where
  p1 : RV
  p2 : RV
  p3 : RV
  p4 : RV

@[expose] def RP.at (P : RP) (e : Nat) : RV :=
  bif e.beq 0 then RV.one else bif e.beq 1 then P.p1 else bif e.beq 2 then P.p2
  else bif e.beq 3 then P.p3 else P.p4

structure RT where
  t0 : RP
  t1 : RP
  t2 : RP
  t3 : RP
  t4 : RP
  t5 : RP

@[expose] def RT.row (T : RT) (i : Nat) : RP :=
  bif i.beq 0 then T.t0 else bif i.beq 1 then T.t1 else bif i.beq 2 then T.t2
  else bif i.beq 3 then T.t3 else bif i.beq 4 then T.t4 else T.t5

@[expose] def applyT (T : RT) (a : RV) : RV :=
  mulR cmM (mulR cmM (mulR cmM (mulR cmM (mulR cmM (mulR cmM (T.t0.at a.a0) (T.t1.at a.a1))
    (T.t2.at a.a2)) (T.t3.at a.a3)) (T.t4.at a.a4)) (T.t5.at a.a5)) (RV.xc a.c)

@[expose] def act1 : RAct :=
  ⟨⟨0, 4, 4, 2, 1, 1, 4⟩, ⟨3, 3, 3, 1, 0, 4, 4⟩, ⟨2, 4, 4, 1, 3, 2, 0⟩, ⟨2, 0, 0, 0, 2, 0, 1⟩,
    ⟨0, 4, 4, 1, 3, 0, 0⟩, ⟨3, 3, 4, 3, 3, 1, 0⟩⟩

@[expose] def act2 : RAct :=
  ⟨⟨3, 0, 3, 2, 1, 0, 2⟩, ⟨3, 3, 4, 2, 3, 4, 3⟩, ⟨0, 0, 2, 4, 4, 0, 2⟩, ⟨0, 3, 1, 4, 3, 1, 4⟩,
    ⟨3, 4, 4, 3, 3, 0, 1⟩, ⟨0, 1, 3, 0, 2, 1, 4⟩⟩

@[expose] def rU : RV := ⟨0, 2, 4, 3, 0, 3, 1⟩

@[expose] def x2 : RV := ⟨0, 0, 0, 0, 0, 0, 2⟩

@[expose] def tabU11 : RT :=
  ⟨⟨⟨1, 1, 0, 4, 2, 0, 4⟩, ⟨2, 2, 0, 3, 4, 0, 1⟩, ⟨3, 3, 0, 2, 1, 0, 1⟩, ⟨4, 4, 0, 1, 3, 0, 4⟩⟩,
    ⟨⟨2, 0, 2, 2, 2, 4, 2⟩, ⟨4, 0, 4, 4, 4, 3, 0⟩, ⟨1, 0, 1, 1, 1, 2, 4⟩, ⟨3, 0, 3, 3, 3, 1, 4⟩⟩,
    ⟨⟨0, 1, 0, 2, 1, 1, 1⟩, ⟨0, 2, 0, 4, 2, 2, 2⟩, ⟨0, 3, 0, 1, 3, 3, 3⟩, ⟨0, 4, 0, 3, 4, 4, 4⟩⟩,
    ⟨⟨0, 4, 2, 2, 0, 0, 3⟩, ⟨0, 3, 4, 4, 0, 0, 4⟩, ⟨0, 2, 1, 1, 0, 0, 3⟩, ⟨0, 1, 3, 3, 0, 0, 0⟩⟩,
    ⟨⟨4, 4, 0, 4, 3, 0, 1⟩, ⟨3, 3, 0, 3, 1, 0, 0⟩, ⟨2, 2, 0, 2, 4, 0, 2⟩, ⟨1, 1, 0, 1, 2, 0, 2⟩⟩,
    ⟨⟨4, 4, 3, 1, 0, 0, 4⟩, ⟨3, 3, 1, 2, 0, 0, 2⟩, ⟨2, 2, 4, 3, 0, 0, 4⟩, ⟨1, 1, 2, 4, 0, 0, 0⟩⟩⟩

@[expose] def tabU12 : RT :=
  ⟨⟨⟨1, 0, 0, 2, 0, 4, 2⟩, ⟨2, 0, 0, 4, 0, 3, 0⟩, ⟨3, 0, 0, 1, 0, 2, 4⟩, ⟨4, 0, 0, 3, 0, 1, 4⟩⟩,
    ⟨⟨1, 1, 1, 3, 2, 2, 4⟩, ⟨2, 2, 2, 1, 4, 4, 4⟩, ⟨3, 3, 3, 4, 1, 1, 0⟩, ⟨4, 4, 4, 2, 3, 3, 2⟩⟩,
    ⟨⟨0, 1, 4, 1, 0, 4, 3⟩, ⟨0, 2, 3, 2, 0, 3, 3⟩, ⟨0, 3, 2, 3, 0, 2, 0⟩, ⟨0, 4, 1, 4, 0, 1, 4⟩⟩,
    ⟨⟨3, 0, 2, 1, 0, 3, 2⟩, ⟨1, 0, 4, 2, 0, 1, 3⟩, ⟨4, 0, 1, 3, 0, 4, 3⟩, ⟨2, 0, 3, 4, 0, 2, 2⟩⟩,
    ⟨⟨4, 2, 1, 4, 0, 1, 0⟩, ⟨3, 4, 2, 3, 0, 2, 0⟩, ⟨2, 1, 3, 2, 0, 3, 0⟩, ⟨1, 3, 4, 1, 0, 4, 0⟩⟩,
    ⟨⟨2, 1, 0, 2, 4, 4, 2⟩, ⟨4, 2, 0, 4, 3, 3, 3⟩, ⟨1, 3, 0, 1, 2, 2, 3⟩, ⟨3, 4, 0, 3, 1, 1, 2⟩⟩⟩

@[expose] def tabU13 : RT :=
  ⟨⟨⟨2, 0, 1, 2, 2, 0, 4⟩, ⟨4, 0, 2, 4, 4, 0, 1⟩, ⟨1, 0, 3, 1, 1, 0, 1⟩, ⟨3, 0, 4, 3, 3, 0, 4⟩⟩,
    ⟨⟨4, 0, 4, 4, 1, 0, 4⟩, ⟨3, 0, 3, 3, 2, 0, 4⟩, ⟨2, 0, 2, 2, 3, 0, 0⟩, ⟨1, 0, 1, 1, 4, 0, 2⟩⟩,
    ⟨⟨3, 4, 1, 1, 1, 3, 2⟩, ⟨1, 3, 2, 2, 2, 1, 4⟩, ⟨4, 2, 3, 3, 3, 4, 1⟩, ⟨2, 1, 4, 4, 4, 2, 3⟩⟩,
    ⟨⟨0, 1, 1, 1, 3, 2, 1⟩, ⟨0, 2, 2, 2, 1, 4, 0⟩, ⟨0, 3, 3, 3, 4, 1, 2⟩, ⟨0, 4, 4, 4, 2, 3, 2⟩⟩,
    ⟨⟨2, 0, 0, 1, 3, 4, 1⟩, ⟨4, 0, 0, 2, 1, 3, 0⟩, ⟨1, 0, 0, 3, 4, 2, 2⟩, ⟨3, 0, 0, 4, 2, 1, 2⟩⟩,
    ⟨⟨1, 2, 3, 4, 3, 4, 1⟩, ⟨2, 4, 1, 3, 1, 3, 3⟩, ⟨3, 1, 4, 2, 4, 2, 1⟩, ⟨4, 3, 2, 1, 2, 1, 0⟩⟩⟩

@[expose] def tabU14 : RT :=
  ⟨⟨⟨0, 4, 4, 2, 1, 1, 4⟩, ⟨0, 3, 3, 4, 2, 2, 0⟩, ⟨0, 2, 2, 1, 3, 3, 3⟩, ⟨0, 1, 1, 3, 4, 4, 3⟩⟩,
    ⟨⟨3, 3, 3, 1, 0, 4, 4⟩, ⟨1, 1, 1, 2, 0, 3, 0⟩, ⟨4, 4, 4, 3, 0, 2, 3⟩, ⟨2, 2, 2, 4, 0, 1, 3⟩⟩,
    ⟨⟨2, 4, 4, 1, 3, 2, 0⟩, ⟨4, 3, 3, 2, 1, 4, 3⟩, ⟨1, 2, 2, 3, 4, 1, 4⟩, ⟨3, 1, 1, 4, 2, 3, 3⟩⟩,
    ⟨⟨2, 0, 0, 0, 2, 0, 1⟩, ⟨4, 0, 0, 0, 4, 0, 2⟩, ⟨1, 0, 0, 0, 1, 0, 3⟩, ⟨3, 0, 0, 0, 3, 0, 4⟩⟩,
    ⟨⟨0, 4, 4, 1, 3, 0, 0⟩, ⟨0, 3, 3, 2, 1, 0, 0⟩, ⟨0, 2, 2, 3, 4, 0, 0⟩, ⟨0, 1, 1, 4, 2, 0, 0⟩⟩,
    ⟨⟨3, 3, 4, 3, 3, 1, 0⟩, ⟨1, 1, 3, 1, 1, 2, 2⟩, ⟨4, 4, 2, 4, 4, 3, 1⟩, ⟨2, 2, 1, 2, 2, 4, 2⟩⟩⟩

@[expose] def tabU21 : RT :=
  ⟨⟨⟨1, 0, 2, 3, 1, 2, 2⟩, ⟨2, 0, 4, 1, 2, 4, 1⟩, ⟨3, 0, 1, 4, 3, 1, 2⟩, ⟨4, 0, 3, 2, 4, 3, 0⟩⟩,
    ⟨⟨3, 0, 3, 4, 2, 1, 3⟩, ⟨1, 0, 1, 3, 4, 2, 2⟩, ⟨4, 0, 4, 2, 1, 3, 2⟩, ⟨2, 0, 2, 1, 3, 4, 3⟩⟩,
    ⟨⟨2, 3, 1, 4, 0, 4, 0⟩, ⟨4, 1, 2, 3, 0, 3, 0⟩, ⟨1, 4, 3, 2, 0, 2, 0⟩, ⟨3, 2, 4, 1, 0, 1, 0⟩⟩,
    ⟨⟨3, 0, 0, 1, 2, 4, 4⟩, ⟨1, 0, 0, 2, 4, 3, 1⟩, ⟨4, 0, 0, 3, 1, 2, 1⟩, ⟨2, 0, 0, 4, 3, 1, 4⟩⟩,
    ⟨⟨1, 1, 1, 2, 3, 4, 3⟩, ⟨2, 2, 2, 4, 1, 3, 0⟩, ⟨3, 3, 3, 1, 4, 2, 1⟩, ⟨4, 4, 4, 3, 2, 1, 1⟩⟩,
    ⟨⟨4, 4, 2, 0, 2, 0, 4⟩, ⟨3, 3, 4, 0, 4, 0, 3⟩, ⟨2, 2, 1, 0, 1, 0, 2⟩, ⟨1, 1, 3, 0, 3, 0, 1⟩⟩⟩

@[expose] def tabU22 : RT :=
  ⟨⟨⟨3, 0, 4, 1, 4, 1, 0⟩, ⟨1, 0, 3, 2, 3, 2, 3⟩, ⟨4, 0, 2, 3, 2, 3, 4⟩, ⟨2, 0, 1, 4, 1, 4, 3⟩⟩,
    ⟨⟨2, 0, 3, 4, 4, 2, 0⟩, ⟨4, 0, 1, 3, 3, 4, 2⟩, ⟨1, 0, 4, 2, 2, 1, 1⟩, ⟨3, 0, 2, 1, 1, 3, 2⟩⟩,
    ⟨⟨1, 4, 2, 1, 4, 2, 1⟩, ⟨2, 3, 4, 2, 3, 4, 3⟩, ⟨3, 2, 1, 3, 2, 1, 1⟩, ⟨4, 1, 3, 4, 1, 3, 0⟩⟩,
    ⟨⟨4, 3, 1, 4, 4, 3, 3⟩, ⟨3, 1, 2, 3, 3, 1, 0⟩, ⟨2, 4, 3, 2, 2, 4, 1⟩, ⟨1, 2, 4, 1, 1, 2, 1⟩⟩,
    ⟨⟨1, 2, 2, 4, 4, 2, 3⟩, ⟨2, 4, 4, 3, 3, 4, 0⟩, ⟨3, 1, 1, 2, 2, 1, 1⟩, ⟨4, 3, 3, 1, 1, 3, 1⟩⟩,
    ⟨⟨2, 3, 4, 0, 3, 3, 1⟩, ⟨4, 1, 3, 0, 1, 1, 4⟩, ⟨1, 4, 2, 0, 4, 4, 4⟩, ⟨3, 2, 1, 0, 2, 2, 1⟩⟩⟩

@[expose] def tabU23 : RT :=
  ⟨⟨⟨2, 0, 1, 4, 4, 2, 1⟩, ⟨4, 0, 2, 3, 3, 4, 0⟩, ⟨1, 0, 3, 2, 2, 1, 2⟩, ⟨3, 0, 4, 1, 1, 3, 2⟩⟩,
    ⟨⟨2, 1, 0, 0, 1, 3, 1⟩, ⟨4, 2, 0, 0, 2, 1, 3⟩, ⟨1, 3, 0, 0, 3, 4, 1⟩, ⟨3, 4, 0, 0, 4, 2, 0⟩⟩,
    ⟨⟨2, 3, 4, 1, 2, 4, 4⟩, ⟨4, 1, 3, 2, 4, 3, 4⟩, ⟨1, 4, 2, 3, 1, 2, 0⟩, ⟨3, 2, 1, 4, 3, 1, 2⟩⟩,
    ⟨⟨3, 4, 3, 0, 1, 2, 2⟩, ⟨1, 3, 1, 0, 2, 4, 1⟩, ⟨4, 2, 4, 0, 3, 1, 2⟩, ⟨2, 1, 2, 0, 4, 3, 0⟩⟩,
    ⟨⟨0, 3, 3, 1, 4, 4, 3⟩, ⟨0, 1, 1, 2, 3, 3, 4⟩, ⟨0, 4, 4, 3, 2, 2, 3⟩, ⟨0, 2, 2, 4, 1, 1, 0⟩⟩,
    ⟨⟨4, 2, 1, 0, 3, 0, 1⟩, ⟨3, 4, 2, 0, 1, 0, 0⟩, ⟨2, 1, 3, 0, 4, 0, 2⟩, ⟨1, 3, 4, 0, 2, 0, 2⟩⟩⟩

@[expose] def tabU24 : RT :=
  ⟨⟨⟨3, 0, 3, 2, 1, 0, 2⟩, ⟨1, 0, 1, 4, 2, 0, 1⟩, ⟨4, 0, 4, 1, 3, 0, 2⟩, ⟨2, 0, 2, 3, 4, 0, 0⟩⟩,
    ⟨⟨3, 3, 4, 2, 3, 4, 3⟩, ⟨1, 1, 3, 4, 1, 3, 1⟩, ⟨4, 4, 2, 1, 4, 2, 4⟩, ⟨2, 2, 1, 3, 2, 1, 2⟩⟩,
    ⟨⟨0, 0, 2, 4, 4, 0, 2⟩, ⟨0, 0, 4, 3, 3, 0, 1⟩, ⟨0, 0, 1, 2, 2, 0, 2⟩, ⟨0, 0, 3, 1, 1, 0, 0⟩⟩,
    ⟨⟨0, 3, 1, 4, 3, 1, 4⟩, ⟨0, 1, 2, 3, 1, 2, 0⟩, ⟨0, 4, 3, 2, 4, 3, 3⟩, ⟨0, 2, 4, 1, 2, 4, 3⟩⟩,
    ⟨⟨3, 4, 4, 3, 3, 0, 1⟩, ⟨1, 3, 3, 1, 1, 0, 1⟩, ⟨4, 2, 2, 4, 4, 0, 0⟩, ⟨2, 1, 1, 2, 2, 0, 3⟩⟩,
    ⟨⟨0, 1, 3, 0, 2, 1, 4⟩, ⟨0, 2, 1, 0, 4, 2, 3⟩, ⟨0, 3, 4, 0, 1, 3, 2⟩, ⟨0, 4, 2, 0, 3, 4, 1⟩⟩⟩

@[expose] def phi1At (k : Nat) (a : RV) : RV :=
  bif k.beq 0 then a else bif k.beq 1 then applyT tabU11 a else bif k.beq 2 then applyT tabU12 a
  else bif k.beq 3 then applyT tabU13 a else applyT tabU14 a

@[expose] def phi2At (k : Nat) (a : RV) : RV :=
  bif k.beq 0 then a else bif k.beq 1 then applyT tabU21 a else bif k.beq 2 then applyT tabU22 a
  else bif k.beq 3 then applyT tabU23 a else applyT tabU24 a

@[expose] def tauAt (e f : Nat) : RV :=
  bif e.beq 0 || f.beq 0 then RV.one
  else bif e.beq 1 then
    (bif f.beq 1 then ⟨0, 1, 4, 3, 4, 0, 2⟩ else bif f.beq 2 then ⟨4, 2, 0, 4, 4, 0, 0⟩
      else bif f.beq 3 then ⟨1, 0, 2, 0, 2, 2, 0⟩ else ⟨0, 2, 4, 3, 0, 3, 1⟩)
  else bif e.beq 2 then
    (bif f.beq 1 then ⟨3, 3, 2, 0, 2, 3, 2⟩ else bif f.beq 2 then ⟨3, 3, 2, 3, 3, 3, 0⟩
      else bif f.beq 3 then ⟨3, 4, 3, 3, 2, 4, 2⟩ else ⟨1, 0, 3, 4, 3, 0, 1⟩)
  else bif e.beq 3 then
    (bif f.beq 1 then ⟨4, 1, 4, 1, 4, 4, 0⟩ else bif f.beq 2 then ⟨2, 3, 1, 2, 2, 4, 1⟩
      else bif f.beq 3 then ⟨1, 2, 3, 4, 0, 1, 1⟩ else ⟨3, 4, 2, 3, 4, 1, 0⟩)
  else
    (bif f.beq 1 then ⟨3, 0, 0, 1, 0, 3, 1⟩ else bif f.beq 2 then ⟨1, 2, 2, 1, 1, 3, 0⟩
      else bif f.beq 3 then ⟨0, 4, 2, 3, 1, 3, 1⟩ else ⟨1, 4, 1, 0, 3, 1, 4⟩)

@[expose] def allBelow (f : Nat → Bool) : Nat → Bool
  | 0 => true
  | k + 1 => f k && allBelow f k

@[expose] def RV.beq (a b : RV) : Bool :=
  a.a0.beq b.a0 && a.a1.beq b.a1 && a.a2.beq b.a2 && a.a3.beq b.a3 && a.a4.beq b.a4 &&
    a.a5.beq b.a5 && a.c.beq b.c

@[expose] def unitR (k : Nat) : RV :=
  ⟨bif k.beq 0 then 1 else 0, bif k.beq 1 then 1 else 0, bif k.beq 2 then 1 else 0,
    bif k.beq 3 then 1 else 0, bif k.beq 4 then 1 else 0, bif k.beq 5 then 1 else 0, 0⟩

@[expose] def RP.powOK (P : RP) : Bool :=
  P.p2.beq (mulR cmM P.p1 P.p1) && P.p3.beq (mulR cmM P.p2 P.p1) && P.p4.beq (mulR cmM P.p3 P.p1)

@[expose] def RT.powOK (T : RT) : Bool := allBelow (fun i => (T.row i).powOK) 6

@[expose] def invOK (A : RAct) (T : RT) : Bool :=
  allBelow (fun i => (applyR cmM A (T.row i).p1).beq (unitR i)) 6

@[expose] def stepOK (T1 T T' : RT) : Bool :=
  allBelow (fun i => (T'.row i).p1.beq (applyT T (T1.row i).p1)) 6

@[expose] def tabOK (_ : Unit := ()) : Bool :=
  tabU11.powOK && tabU12.powOK && tabU13.powOK && tabU14.powOK && invOK act1 tabU11 &&
    stepOK tabU11 tabU11 tabU12 && stepOK tabU11 tabU12 tabU13 && stepOK tabU11 tabU13 tabU14 &&
  tabU21.powOK && tabU22.powOK && tabU23.powOK && tabU24.powOK && invOK act2 tabU21 &&
    stepOK tabU21 tabU21 tabU22 && stepOK tabU21 tabU22 tabU23 && stepOK tabU21 tabU23 tabU24

@[expose] def tauOK (_ : Unit := ()) : Bool :=
  (mulR cmM rU (applyR cmM act2 (tauAt 1 1))).beq RV.one &&
    allBelow (fun f => (tauAt 1 (f + 2)).beq (mulR cmM (tauAt 1 1) (phi2At 1 (tauAt 1 (f + 1))))) 3 &&
    allBelow (fun e => allBelow (fun f =>
      (tauAt (e + 2) (f + 1)).beq (mulR cmM (phi1At 1 (tauAt (e + 1) (f + 1))) (tauAt 1 (f + 1)))) 4) 3

@[expose] def encA (a : RV) : Nat :=
  3125 * a.a0 + 625 * a.a1 + 125 * a.a2 + 25 * a.a3 + 5 * a.a4 + a.a5

@[expose] def actRow (i j k : Nat) : RV := phi1At j (phi2At i (unitR k))

@[expose] def sig (i j : Nat) : Nat :=
  encA (actRow i j 0) + 15625 * (encA (actRow i j 1) + 15625 * (encA (actRow i j 2) +
    15625 * (encA (actRow i j 3) + 15625 * (encA (actRow i j 4) + 15625 * encA (actRow i j 5)))))

@[expose] def sigOK (_ : Unit := ()) : Bool :=
  allBelow (fun p => allBelow (fun q => !(sig (p / 5) (p % 5)).beq (sig (q / 5) (q % 5))) p) 25

structure V9 where
  e0 : Nat
  e1 : Nat
  r : RV

@[expose] def V9.one : V9 := ⟨0, 0, RV.one⟩

@[expose] def V9.beq (v w : V9) : Bool := v.e0.beq w.e0 && v.e1.beq w.e1 && v.r.beq w.r

@[expose] def V9.isOne (v : V9) : Bool := v.beq V9.one

@[expose] def decR (n : Nat) : RV :=
  ⟨n / 15625 % 5, n / 3125 % 5, n / 625 % 5, n / 125 % 5, n / 25 % 5, n / 5 % 5, n % 5⟩

@[expose] def dec (i : Nat) : V9 := ⟨i / 390625 % 5, i / 78125 % 5, decR (i % 78125)⟩

@[expose] def carry (e f : Nat) : RV := bif Nat.blt (e + f) 5 then RV.one else x2

@[expose] def mulV (v w : V9) : V9 :=
  ⟨(v.e0 + w.e0) % 5, (v.e1 + w.e1) % 5,
    mulR cmM (mulR cmM (mulR cmM (carry v.e1 w.e1) (phi1At w.e1 (tauAt v.e1 w.e0)))
      (phi1At w.e1 (phi2At w.e0 v.r))) w.r⟩

@[expose] def powV (v : V9) : Nat → V9
  | 0 => V9.one
  | k + 1 => mulV (powV v k) v

@[expose] def ord5 (v : V9) : Bool := (powV v 5).isOne

end CFSG.KC.MonPcFive

end
