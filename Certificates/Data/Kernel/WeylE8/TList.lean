module

public import Certificates.Data.Kernel.WeylE8.SP

public section

namespace CFSG.KLC.E8

open CFSG.KC.Enum

@[expose] noncomputable def e24 (P k : Nat) : Nat := pg (nat_lit 24) (nat_lit 16777215) P k

@[expose] noncomputable def e32 (P k : Nat) : Nat := pg (nat_lit 32) (nat_lit 4294967295) P k

@[expose] noncomputable def evenMaskK (r : Nat) : Nat :=
  Nat.add (Nat.mul (nat_lit 2) r) (Nat.land (pop8 r) (nat_lit 1))

@[expose] noncomputable def tcK (PP i : Nat) : Nat :=
  Nat.add (e24 PP (Nat.shiftRight i (nat_lit 7)))
    (Nat.shiftLeft (evenMaskK (Nat.land i (nat_lit 127))) (nat_lit 24))

@[expose] noncomputable def negC : Nat := nat_lit 4294624904

@[expose] noncomputable def s0C : Nat := nat_lit 16434817

@[expose] noncomputable def permOKK (c : Nat) : Bool :=
  allN (nat_lit 8) fun j => notB' (allN (nat_lit 8) fun k => notB' (Nat.beq (spAt c k) j))

@[expose] noncomputable def okC (c : Nat) : Bool :=
  bAnd(Nat.blt c (nat_lit 4294967296), bAnd(permOKK c, evenB (spMask c)))

@[expose] noncomputable def invoK (c : Nat) : Bool := Nat.beq (spMul c c) spId

@[expose] noncomputable def commK' (c d : Nat) : Bool := Nat.beq (spMul c d) (spMul d c)

@[expose] noncomputable def jdxK (PP MT GC : Nat) (i k : Nat) : Nat :=
  Nat.add (Nat.mul (nat_lit 128)
      (nIf(Nat.blt k (nat_lit 7), Nat.shiftRight i (nat_lit 7),
        pg (nat_lit 8) (nat_lit 255) MT
          (Nat.add (Nat.mul (nat_lit 6) (Nat.shiftRight i (nat_lit 7))) (Nat.sub k (nat_lit 7))))))
    (Nat.shiftRight (spMask (spMul (e32 GC k) (tcK PP i))) (nat_lit 1))

@[expose] noncomputable def rangeK (f : Nat → Bool) (lo n : Nat) : Bool :=
  allN n fun i => f (Nat.add lo i)

@[expose] noncomputable def closedAt (PP MT GC i : Nat) : Bool :=
  bAnd(okC (tcK PP i), allN (nat_lit 13) fun k => strictB (jdxK PP MT GC i k) fun j =>
    bAnd(Nat.blt j (nat_lit 8192), Nat.beq (tcK PP j) (spMul (e32 GC k) (tcK PP i))))

@[expose] noncomputable def treeAt (PP MT GC i : Nat) : Bool :=
  bIf(Nat.beq i (nat_lit 0), true, notB' (allN (nat_lit 13) fun k =>
    strictB (jdxK PP MT GC i k) fun j =>
      notB' (bAnd(Nat.blt j i, Nat.beq (spMul (e32 GC k) (tcK PP j)) (tcK PP i)))))

@[expose] noncomputable def gensK (GC RH RHI : Nat) : Bool :=
  bAnd(allN (nat_lit 13) (fun k => strictB (e32 GC k) fun g => bAnd(okC g, invoK g)),
  bAnd(okC s0C, bAnd(okC negC, bAnd(okC spId,
    allN (nat_lit 25) fun k => strictB (e32 RH k) fun r => strictB (e32 RHI k) fun ri =>
      bAnd(okC r, bAnd(okC ri, Nat.beq (spMul r ri) spId))))))

@[expose] noncomputable def s0K (PP GC S0J : Nat) : Bool :=
  allN (nat_lit 13) fun k => strictB (pg (nat_lit 16) (nat_lit 65535) S0J k) fun j =>
    strictB (spMul (e32 GC k) s0C) fun gs => bAnd(okC gs,
      bAnd(Nat.blt j (nat_lit 8192), Nat.beq (tcK PP j) (spMul s0C gs)))

@[expose] noncomputable def frameK' (c : Nat) : Bool :=
  allN (nat_lit 4) fun j => strictB (Nat.mul (nat_lit 2) j) fun a =>
    bAnd(bIf(Nat.beq (spAt c a) a, Nat.beq (spAt c (Nat.succ a)) (Nat.succ a),
        bAnd(Nat.beq (spAt c a) (Nat.succ a), Nat.beq (spAt c (Nat.succ a)) a)),
      Nat.beq (Nat.land (Nat.shiftRight (spMask c) a) (nat_lit 1))
        (Nat.land (Nat.shiftRight (spMask c) (Nat.succ a)) (nat_lit 1)))

@[expose] noncomputable def fgK (t : Nat) : Bool :=
  notB' (allN (nat_lit 8) fun a => allN a fun b =>
    strictB (Nat.add (Nat.shiftLeft (Nat.add (Nat.shiftLeft (nat_lit 1) a) (Nat.shiftLeft (nat_lit 1) b))
      (nat_lit 24)) spId) fun s => strictB (spMul s t) fun u => strictB (spMul u u) fun c =>
        notB' (bAnd(notB' (Nat.beq c spId), bAnd(notB' (Nat.beq c negC), invoK c))))

@[expose] noncomputable def w8K (RH RHI t : Nat) : Bool :=
  notB' (allN (nat_lit 25) fun k => strictB (spMul (e32 RH k) t) fun u =>
    strictB (spMul u (e32 RHI k)) fun v => notB' (frameK' v))

@[expose] noncomputable def factAtK (GC RH RHI : Nat) (b : Bool) (t : Nat) : Bool :=
  strictB (spMul t t) fun t2 =>
  bAnd(bIf(b, notB' (Nat.beq t2 negC), true),
  bAnd(bIf(b, bIf(Nat.beq t2 spId, fgK t, true), true),
  bAnd(bIf(Nat.beq t2 spId, bIf(Nat.beq t spId, true, w8K RH RHI t), true),
  bAnd(bIf(bAnd(allN (nat_lit 13) (fun k => commK' t (e32 GC k)), commK' t s0C),
      bIf(Nat.beq t spId, true, Nat.beq t negC), true),
    bIf(b, true, bIf(allN (nat_lit 13) (fun k => commK' t (e32 GC k)),
      bIf(Nat.beq t spId, true, Nat.beq t negC), true))))))

@[expose] noncomputable def reflCodeK (DP r : Nat) : Nat :=
  strictN (Nat.shiftRight r (nat_lit 2)) fun p => strictN (pa DP p) fun a => strictN (pb DP p) fun b =>
    strictN (Nat.land r (nat_lit 3)) fun s =>
      Nat.add (Nat.add (Nat.sub spId (Nat.add (Nat.shiftLeft a (Nat.mul (nat_lit 3) a))
          (Nat.shiftLeft b (Nat.mul (nat_lit 3) b))))
        (Nat.add (Nat.shiftLeft b (Nat.mul (nat_lit 3) a)) (Nat.shiftLeft a (Nat.mul (nat_lit 3) b))))
        (nIf(bIf(Nat.beq s (nat_lit 0), true, Nat.beq s (nat_lit 3)),
          Nat.shiftLeft (Nat.add (Nat.shiftLeft (nat_lit 1) a) (Nat.shiftLeft (nat_lit 1) b)) (nat_lit 24),
          nat_lit 0))

@[expose] noncomputable def wordCodeK (DP : Nat) (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) spId (fun r _ ih => spMul (reflCodeK DP r) ih) l

@[expose] noncomputable def wordOKK (DP : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun r l ih => bAnd(Nat.blt r (nat_lit 112),
    bAnd(okC (reflCodeK DP r), bAnd(okC (wordCodeK DP l), ih)))) l

@[expose] noncomputable def wordsK (DP : Nat) (W : Nat → List Nat) (n C : Nat) : Bool :=
  allN n fun k => bAnd(wordOKK DP (W k), Nat.beq (wordCodeK DP (W k)) (e32 C k))

@[expose] noncomputable def factsAt (PP GC RH RHI i : Nat) : Bool :=
  strictB (tcK PP i) fun t =>
    bAnd(factAtK GC RH RHI false t, factAtK GC RH RHI true (spMul t s0C))

end CFSG.KLC.E8

end
