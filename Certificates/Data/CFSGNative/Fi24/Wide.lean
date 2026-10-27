module

public section

namespace CFSG.Sporadic.Fi24.Native

structure W where
  p0 : UInt64
  p1 : UInt64
  p2 : UInt64
  p3 : UInt64
  p4 : UInt64
  p5 : UInt64
  p6 : UInt64
  p7 : UInt64
  p8 : UInt64
  p9 : UInt64
  p10 : UInt64
  p11 : UInt64
  p12 : UInt64
  m0 : UInt64
  m1 : UInt64
  m2 : UInt64
  m3 : UInt64
  m4 : UInt64
  m5 : UInt64
  m6 : UInt64
  m7 : UInt64
  m8 : UInt64
  m9 : UInt64
  m10 : UInt64
  m11 : UInt64
  m12 : UInt64
deriving Inhabited, DecidableEq

@[inline, expose] def sumT (ap am bp bm : UInt64) : UInt64 := (ap ||| bm) ^^^ (am ||| bp)

@[inline, expose] def sumP (ap am bp bm : UInt64) : UInt64 := (am ||| bm) ^^^ sumT ap am bp bm

@[inline, expose] def sumM (ap am bp bm : UInt64) : UInt64 := (ap ||| bp) ^^^ sumT ap am bp bm

@[inline, expose] def W.add (a b : W) : W :=
  let t0 := sumT a.p0 a.m0 b.p0 b.m0
  let t1 := sumT a.p1 a.m1 b.p1 b.m1
  let t2 := sumT a.p2 a.m2 b.p2 b.m2
  let t3 := sumT a.p3 a.m3 b.p3 b.m3
  let t4 := sumT a.p4 a.m4 b.p4 b.m4
  let t5 := sumT a.p5 a.m5 b.p5 b.m5
  let t6 := sumT a.p6 a.m6 b.p6 b.m6
  let t7 := sumT a.p7 a.m7 b.p7 b.m7
  let t8 := sumT a.p8 a.m8 b.p8 b.m8
  let t9 := sumT a.p9 a.m9 b.p9 b.m9
  let t10 := sumT a.p10 a.m10 b.p10 b.m10
  let t11 := sumT a.p11 a.m11 b.p11 b.m11
  let t12 := sumT a.p12 a.m12 b.p12 b.m12
  ⟨(a.m0 ||| b.m0) ^^^ t0, (a.m1 ||| b.m1) ^^^ t1, (a.m2 ||| b.m2) ^^^ t2, (a.m3 ||| b.m3) ^^^ t3,
    (a.m4 ||| b.m4) ^^^ t4, (a.m5 ||| b.m5) ^^^ t5, (a.m6 ||| b.m6) ^^^ t6, (a.m7 ||| b.m7) ^^^ t7,
    (a.m8 ||| b.m8) ^^^ t8, (a.m9 ||| b.m9) ^^^ t9, (a.m10 ||| b.m10) ^^^ t10,
    (a.m11 ||| b.m11) ^^^ t11, (a.m12 ||| b.m12) ^^^ t12, (a.p0 ||| b.p0) ^^^ t0,
    (a.p1 ||| b.p1) ^^^ t1, (a.p2 ||| b.p2) ^^^ t2, (a.p3 ||| b.p3) ^^^ t3, (a.p4 ||| b.p4) ^^^ t4,
    (a.p5 ||| b.p5) ^^^ t5, (a.p6 ||| b.p6) ^^^ t6, (a.p7 ||| b.p7) ^^^ t7, (a.p8 ||| b.p8) ^^^ t8,
    (a.p9 ||| b.p9) ^^^ t9, (a.p10 ||| b.p10) ^^^ t10, (a.p11 ||| b.p11) ^^^ t11,
    (a.p12 ||| b.p12) ^^^ t12⟩

@[inline, expose] def W.neg (a : W) : W :=
  ⟨a.m0, a.m1, a.m2, a.m3, a.m4, a.m5, a.m6, a.m7, a.m8, a.m9, a.m10, a.m11, a.m12, a.p0, a.p1,
    a.p2, a.p3, a.p4, a.p5, a.p6, a.p7, a.p8, a.p9, a.p10, a.p11, a.p12⟩

@[inline, expose] def W.sub (a b : W) : W :=
  let t0 := sumT a.p0 a.m0 b.m0 b.p0
  let t1 := sumT a.p1 a.m1 b.m1 b.p1
  let t2 := sumT a.p2 a.m2 b.m2 b.p2
  let t3 := sumT a.p3 a.m3 b.m3 b.p3
  let t4 := sumT a.p4 a.m4 b.m4 b.p4
  let t5 := sumT a.p5 a.m5 b.m5 b.p5
  let t6 := sumT a.p6 a.m6 b.m6 b.p6
  let t7 := sumT a.p7 a.m7 b.m7 b.p7
  let t8 := sumT a.p8 a.m8 b.m8 b.p8
  let t9 := sumT a.p9 a.m9 b.m9 b.p9
  let t10 := sumT a.p10 a.m10 b.m10 b.p10
  let t11 := sumT a.p11 a.m11 b.m11 b.p11
  let t12 := sumT a.p12 a.m12 b.m12 b.p12
  ⟨(a.m0 ||| b.p0) ^^^ t0, (a.m1 ||| b.p1) ^^^ t1, (a.m2 ||| b.p2) ^^^ t2, (a.m3 ||| b.p3) ^^^ t3,
    (a.m4 ||| b.p4) ^^^ t4, (a.m5 ||| b.p5) ^^^ t5, (a.m6 ||| b.p6) ^^^ t6, (a.m7 ||| b.p7) ^^^ t7,
    (a.m8 ||| b.p8) ^^^ t8, (a.m9 ||| b.p9) ^^^ t9, (a.m10 ||| b.p10) ^^^ t10,
    (a.m11 ||| b.p11) ^^^ t11, (a.m12 ||| b.p12) ^^^ t12, (a.p0 ||| b.m0) ^^^ t0,
    (a.p1 ||| b.m1) ^^^ t1, (a.p2 ||| b.m2) ^^^ t2, (a.p3 ||| b.m3) ^^^ t3, (a.p4 ||| b.m4) ^^^ t4,
    (a.p5 ||| b.m5) ^^^ t5, (a.p6 ||| b.m6) ^^^ t6, (a.p7 ||| b.m7) ^^^ t7, (a.p8 ||| b.m8) ^^^ t8,
    (a.p9 ||| b.m9) ^^^ t9, (a.p10 ||| b.m10) ^^^ t10, (a.p11 ||| b.m11) ^^^ t11,
    (a.p12 ||| b.m12) ^^^ t12⟩

@[inline, expose] def W.zero : W :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

@[inline, expose] def W.limbP (a : W) (l : Nat) : UInt64 :=
  if l = 0 then a.p0 else if l = 1 then a.p1 else if l = 2 then a.p2 else if l = 3 then a.p3 else
  if l = 4 then a.p4 else if l = 5 then a.p5 else if l = 6 then a.p6 else if l = 7 then a.p7 else
  if l = 8 then a.p8 else if l = 9 then a.p9 else if l = 10 then a.p10 else
  if l = 11 then a.p11 else if l = 12 then a.p12 else 0

@[inline, expose] def W.limbM (a : W) (l : Nat) : UInt64 :=
  if l = 0 then a.m0 else if l = 1 then a.m1 else if l = 2 then a.m2 else if l = 3 then a.m3 else
  if l = 4 then a.m4 else if l = 5 then a.m5 else if l = 6 then a.m6 else if l = 7 then a.m7 else
  if l = 8 then a.m8 else if l = 9 then a.m9 else if l = 10 then a.m10 else
  if l = 11 then a.m11 else if l = 12 then a.m12 else 0

@[inline, expose] def W.bitP (a : W) (j : Nat) : Bool :=
  (a.limbP (j >>> 6) >>> (j &&& 63).toUInt64) &&& 1 != 0

@[inline, expose] def W.bitM (a : W) (j : Nat) : Bool :=
  (a.limbM (j >>> 6) >>> (j &&& 63).toUInt64) &&& 1 != 0

@[inline, expose] def W.trit (a : W) (j : Nat) : Nat :=
  if a.bitP j then 1 else if a.bitM j then 2 else 0

@[expose] def W.setTrit (a : W) (j z : Nat) : W :=
  let b : UInt64 := (1 : UInt64) <<< (j &&& 63).toUInt64
  let l := j >>> 6
  if z = 1 then
    if l = 0 then { a with p0 := a.p0 ||| b }
    else if l = 1 then { a with p1 := a.p1 ||| b }
    else if l = 2 then { a with p2 := a.p2 ||| b }
    else if l = 3 then { a with p3 := a.p3 ||| b }
    else if l = 4 then { a with p4 := a.p4 ||| b }
    else if l = 5 then { a with p5 := a.p5 ||| b }
    else if l = 6 then { a with p6 := a.p6 ||| b }
    else if l = 7 then { a with p7 := a.p7 ||| b }
    else if l = 8 then { a with p8 := a.p8 ||| b }
    else if l = 9 then { a with p9 := a.p9 ||| b }
    else if l = 10 then { a with p10 := a.p10 ||| b }
    else if l = 11 then { a with p11 := a.p11 ||| b }
    else { a with p12 := a.p12 ||| b }
  else if z = 2 then
    if l = 0 then { a with m0 := a.m0 ||| b }
    else if l = 1 then { a with m1 := a.m1 ||| b }
    else if l = 2 then { a with m2 := a.m2 ||| b }
    else if l = 3 then { a with m3 := a.m3 ||| b }
    else if l = 4 then { a with m4 := a.m4 ||| b }
    else if l = 5 then { a with m5 := a.m5 ||| b }
    else if l = 6 then { a with m6 := a.m6 ||| b }
    else if l = 7 then { a with m7 := a.m7 ||| b }
    else if l = 8 then { a with m8 := a.m8 ||| b }
    else if l = 9 then { a with m9 := a.m9 ||| b }
    else if l = 10 then { a with m10 := a.m10 ||| b }
    else if l = 11 then { a with m11 := a.m11 ||| b }
    else { a with m12 := a.m12 ||| b }
  else a

@[inline, expose] def W.wf (a : W) : Bool :=
  a.p0 &&& a.m0 == 0 && a.p1 &&& a.m1 == 0 && a.p2 &&& a.m2 == 0 && a.p3 &&& a.m3 == 0 &&
    a.p4 &&& a.m4 == 0 && a.p5 &&& a.m5 == 0 && a.p6 &&& a.m6 == 0 && a.p7 &&& a.m7 == 0 &&
    a.p8 &&& a.m8 == 0 && a.p9 &&& a.m9 == 0 && a.p10 &&& a.m10 == 0 && a.p11 &&& a.m11 == 0 &&
    a.p12 &&& a.m12 == 0

@[inline, expose] def W.canon (a : W) : Bool :=
  a.wf && a.p12 >>> 13 == 0 && a.m12 >>> 13 == 0

@[inline, expose] def W.isZero (a : W) : Bool :=
  a.p0 == 0 && a.p1 == 0 && a.p2 == 0 && a.p3 == 0 && a.p4 == 0 && a.p5 == 0 && a.p6 == 0 &&
    a.p7 == 0 && a.p8 == 0 && a.p9 == 0 && a.p10 == 0 && a.p11 == 0 && a.p12 == 0 && a.m0 == 0 &&
    a.m1 == 0 && a.m2 == 0 && a.m3 == 0 && a.m4 == 0 && a.m5 == 0 && a.m6 == 0 && a.m7 == 0 &&
    a.m8 == 0 && a.m9 == 0 && a.m10 == 0 && a.m11 == 0 && a.m12 == 0

@[inline, expose] def W.restrictEq (a M U : W) : Bool :=
  a.p0 &&& M.p0 == U.p0 && a.p1 &&& M.p1 == U.p1 && a.p2 &&& M.p2 == U.p2 &&
    a.p3 &&& M.p3 == U.p3 && a.p4 &&& M.p4 == U.p4 && a.p5 &&& M.p5 == U.p5 &&
    a.p6 &&& M.p6 == U.p6 && a.p7 &&& M.p7 == U.p7 && a.p8 &&& M.p8 == U.p8 &&
    a.p9 &&& M.p9 == U.p9 && a.p10 &&& M.p10 == U.p10 && a.p11 &&& M.p11 == U.p11 &&
    a.p12 &&& M.p12 == U.p12 && a.m0 &&& M.p0 == 0 && a.m1 &&& M.p1 == 0 && a.m2 &&& M.p2 == 0 &&
    a.m3 &&& M.p3 == 0 && a.m4 &&& M.p4 == 0 && a.m5 &&& M.p5 == 0 && a.m6 &&& M.p6 == 0 &&
    a.m7 &&& M.p7 == 0 && a.m8 &&& M.p8 == 0 && a.m9 &&& M.p9 == 0 && a.m10 &&& M.p10 == 0 &&
    a.m11 &&& M.p11 == 0 && a.m12 &&& M.p12 == 0

@[inline, expose] def W.orP (a b : W) : W :=
  ⟨a.p0 ||| b.p0, a.p1 ||| b.p1, a.p2 ||| b.p2, a.p3 ||| b.p3, a.p4 ||| b.p4, a.p5 ||| b.p5,
    a.p6 ||| b.p6, a.p7 ||| b.p7, a.p8 ||| b.p8, a.p9 ||| b.p9, a.p10 ||| b.p10, a.p11 ||| b.p11,
    a.p12 ||| b.p12, a.m0, a.m1, a.m2, a.m3, a.m4, a.m5, a.m6, a.m7, a.m8, a.m9, a.m10, a.m11,
    a.m12⟩

end CFSG.Sporadic.Fi24.Native
