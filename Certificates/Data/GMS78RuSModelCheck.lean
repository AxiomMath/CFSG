module

public import Certificates.Data.GMS78RuSModelData

public section

namespace CFSG.GMS78RuS

open CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuQ

@[expose] def gamArr : Array (Fin 8) := (Array.range 65536).map fun i => gam (i / 256) (i % 256)

@[expose] def dPartArr : Array (Nat × Fin 8) :=
  (Array.range 2048).map fun i => dPart (fin8Of (i / 256)) (i % 256)

@[expose] def sMulF (ε : Bool) (p q : Nat × Fin 8 × Fin 8) : Nat × Fin 8 × Fin 8 :=
  let dp := dPartArr.getD (256 * p.2.2.val + q.1) (0, 0)
  (p.1 ^^^ dp.1,
    p.2.1 ^^^ linApply (dCode p.2.2) q.2.1 ^^^ dp.2 ^^^ gamArr.getD (256 * p.1 + dp.1) 0 ^^^
      (if ε && dOvf p.2.2 q.2.2 then 1 else 0),
    dMul p.2.2 q.2.2)

@[expose] def s0d (j : Nat) : Fin 8 := [0, 3, 4, 7].getD j 0

@[expose] def s0dIdx (d : Fin 8) : Nat := d.val / 2

@[expose] def lift16 (p : Nat) : Nat × Fin 8 × Fin 8 :=
  (p % 256, fin8Of (4 * ((p / 256) % 2)), s0d (p / 512))

@[expose] def enc16 (x : Nat × Fin 8 × Fin 8) : Nat :=
  x.1 + 256 * (x.2.1.val / 4) + 512 * s0dIdx x.2.2

@[expose] def mul16 (ε : Bool) (p q : Nat) : Nat := enc16 (sMulF ε (lift16 p) (lift16 q))

@[expose] def inv16 (ε : Bool) : List Nat :=
  (List.range 2048).filter fun u => mul16 ε u u == 0 && u != 0 && u != 256

@[expose] def cent16 (ε : Bool) (u : Nat) : List Nat :=
  (List.range 2048).filter fun p => mul16 ε p u == mul16 ε u p

@[expose] def cntR16 (ε : Bool) (C : List Nat) (t : Nat) : Nat :=
  C.countP fun p => mul16 ε p p == t

@[expose] def key16 (ε : Bool) (u : Nat) : Nat × Nat × Nat × Nat :=
  let C := cent16 ε u
  (u, C.length, cntR16 ε C u, cntR16 ε C 256)

@[expose] def conjSq16 (ε : Bool) (u : Nat) : Bool :=
  (cent16 ε u).any fun p => mul16 ε p p != 0 &&
    (List.range 2048).any fun w => mul16 ε w u == mul16 ε (mul16 ε u (mul16 ε p p)) w

@[expose] def check16 (ε : Bool) : Bool :=
  let K := (inv16 ε).map (key16 ε)
  (K.all fun a => K.all fun b =>
    !(a.2.1 == b.2.1 && a.2.2.1 == b.2.2.2 && a.2.2.2 == b.2.2.1) || a.2.1 == 128) &&
  (K.all fun a => a.2.1 != 128 || conjSq16 ε a.1) &&
  ((List.range 2048).all fun p => mul16 ε 256 (mul16 ε p p) / 512 == 0) &&
  (K.all fun a => a.1 / 512 != 0 || a.2.1 != 128) &&
  ((List.range 2048).all fun p => mul16 ε p 256 == mul16 ε 256 p)

@[expose] def lift17 (p : Nat) : Nat × Fin 8 × Fin 8 :=
  (p % 256, fin8Of (2 * ((p / 256) % 4)), fin8Of (p / 1024))

@[expose] def enc17 (x : Nat × Fin 8 × Fin 8) : Nat :=
  x.1 + 256 * (x.2.1.val / 2) + 1024 * x.2.2.val

@[expose] def mul17 (ε : Bool) (p q : Nat) : Nat := enc17 (sMulF ε (lift17 p) (lift17 q))

@[expose] def inX17 (u : Nat) : Bool := u / 1024 == 0 && sMask (u % 256) < 4

@[expose] def inv17 (ε : Bool) : List Nat :=
  (List.range 8192).filter fun u => mul17 ε u u == 0 && u != 0 && u != 256

@[expose] def cent17 (ε : Bool) (u : Nat) : List Nat :=
  (List.range 8192).filter fun p => mul17 ε p u == mul17 ε u p

@[expose] def cntR17 (ε : Bool) (C : List Nat) (t : Nat) : Nat :=
  C.countP fun p => mul17 ε p p == t

@[expose] def zx17 (ε : Bool) (C : List Nat) (t : Nat) : Nat :=
  C.countP fun p => C.all fun q =>
    mul17 ε p q == mul17 ε q p || mul17 ε p q == mul17 ε t (mul17 ε q p)

@[expose] def needZ17 (u n r r' : Nat) : Bool := u / 1024 != 0 && n == 256 && r == r'

@[expose] def key17 (ε : Bool) (u : Nat) : Nat × Nat × Nat × Nat × Nat × Nat :=
  let C := cent17 ε u
  let r := cntR17 ε C u
  let r' := cntR17 ε C 256
  (u, C.length, r, r',
    if needZ17 u C.length r r' then zx17 ε C u else 0,
    if needZ17 u C.length r r' then zx17 ε C 256 else 0)

@[expose] def check17 (ε : Bool) : Bool :=
  let K := (inv17 ε).map (key17 ε)
  ((List.range 8192).all fun p => mul17 ε p 256 == mul17 ε 256 p) &&
  K.all fun a => inX17 a.1 || K.all fun b =>
    !(a.2.1 == b.2.1 && a.2.2.1 == b.2.2.2.1 && a.2.2.2.1 == b.2.2.1) ||
      (a.2.1 == 128 && (a.1 / 1024 == 1 || a.1 / 1024 == 5)) ||
      (needZ17 a.1 a.2.1 a.2.2.1 a.2.2.2.1 && needZ17 b.1 b.2.1 b.2.2.1 b.2.2.2.1 &&
        (a.2.2.2.2.1 != b.2.2.2.2.2 || a.2.2.2.2.2 != b.2.2.2.2.1))

end CFSG.GMS78RuS
