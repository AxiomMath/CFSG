module

public import Certificates.Data.Kernel.SporSch.TitsPrim
public import Certificates.Data.Kernel.O8.Nat8

public section

namespace CFSG.KC.AS81

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch

@[expose] noncomputable def filtStep (p : Nat → Bool) (R : Nat → Nat) (i s : Nat) : Nat :=
  nIf(Nat.beq (Nat.land s (nat_lit 1)) (nat_lit 1), s,
    nIf(p i, nIf(Nat.beq (R (Nat.shiftRight s (nat_lit 1))) i, Nat.add s (nat_lit 2), nat_lit 1),
      s))

@[expose] noncomputable def filtK (p : Nat → Bool) (R : Nat → Nat) (N cnt : Nat) : Bool :=
  Nat.beq (foldUp N (filtStep p R) (nat_lit 0)) (Nat.mul (nat_lit 2) cnt)

@[expose] noncomputable def plK (PR : Nat → Nat) (x y : Nat) : Nat := pg 11 (nat_lit 2047) (PR x) y

@[expose] noncomputable def ltK (LT : Nat → Nat) (j t : Nat) : Nat := pgW 7 (LT j) t

@[expose] noncomputable def onK (LT : Nat → Nat) (t x : Nat) : Bool :=
  bIf(Nat.beq x (ltK LT 0 t), true, bIf(Nat.beq x (ltK LT 1 t), true, Nat.beq x (ltK LT 2 t)))

@[expose] noncomputable def pairIn (a b c x y : Nat) : Bool :=
  bIf(bAnd(Nat.beq x a, Nat.beq y b), true, bIf(bAnd(Nat.beq x b, Nat.beq y a), true,
  bIf(bAnd(Nat.beq x a, Nat.beq y c), true, bIf(bAnd(Nat.beq x c, Nat.beq y a), true,
  bIf(bAnd(Nat.beq x b, Nat.beq y c), true, bAnd(Nat.beq x c, Nat.beq y b))))))

@[expose] noncomputable def lineK (LT PR : Nat → Nat) : Bool :=
  allN (nat_lit 1120) (fun t => strictB (ltK LT 0 t) (fun a => strictB (ltK LT 1 t) (fun b =>
    strictB (ltK LT 2 t) (fun c =>
    bAnd(Nat.blt a b, bAnd(Nat.blt b c, bAnd(Nat.blt c (nat_lit 120),
    bAnd(Nat.beq (plK PR a b) t, bAnd(Nat.beq (plK PR b a) t, bAnd(Nat.beq (plK PR a c) t,
    bAnd(Nat.beq (plK PR c a) t, bAnd(Nat.beq (plK PR b c) t, Nat.beq (plK PR c b) t))))))))))))

@[expose] noncomputable def tabK (LT PR : Nat → Nat) : Bool :=
  allN (nat_lit 120) (fun x => allN (nat_lit 120) (fun y => strictB (plK PR x y) (fun t =>
    bIf(Nat.beq t (nat_lit 0), true, bAnd(Nat.blt t (nat_lit 1120),
      pairIn (ltK LT 0 t) (ltK LT 1 t) (ltK LT 2 t) x y)))))

@[expose] noncomputable def nsK (NS a : Nat) : Nat := pg 8 (nat_lit 255) NS a

@[expose] noncomputable def thirdK (NS NI a b : Nat) : Nat :=
  pg 8 (nat_lit 255) NI (Nat.xor (nsK NS a) (nsK NS b))

@[expose] noncomputable def headK (NS NI a b : Nat) : Bool :=
  bAnd(Nat.blt a b, bAnd(Nat.beq (CFSG.KC.O8.b8K false (nsK NS a) (nsK NS b)) (nat_lit 1),
    Nat.blt b (thirdK NS NI a b)))

@[expose] noncomputable def keyHeadK (NS NI k : Nat) : Bool :=
  headK NS NI (Nat.div k (nat_lit 120)) (Nat.mod k (nat_lit 120))

@[expose] noncomputable def lkeyK (LT : Nat → Nat) (t : Nat) : Nat :=
  Nat.add (Nat.mul (nat_lit 120) (ltK LT 0 t)) (ltK LT 1 t)

@[expose] noncomputable def linesK (NS NI : Nat) (LT : Nat → Nat) : Bool :=
  bAnd(filtK (keyHeadK NS NI) (lkeyK LT) (nat_lit 14400) (nat_lit 1120),
    allN (nat_lit 1120) (fun t => Nat.beq (ltK LT 2 t) (thirdK NS NI (ltK LT 0 t) (ltK LT 1 t))))

@[expose] noncomputable def ptsK (NS NI : Nat) (O : Nat → Nat) : Bool :=
  allN (nat_lit 8) (fun i => allN (nat_lit 120) (fun j => strictB (pg 7 (nat_lit 127) (O i) j)
    (fun y => bAnd(Nat.blt y (nat_lit 120), Nat.beq y (pg 8 (nat_lit 255) NI
      (CFSG.KC.O8.eichK false (pg 8 (nat_lit 255) CFSG.KC.O8.RP (Nat.mul (nat_lit 6) i))
        (pg 8 (nat_lit 255) CFSG.KC.O8.RP (Nat.succ (Nat.mul (nat_lit 6) i))) (nsK NS j)))))))

@[expose] noncomputable def pairK (NS NI : Nat) (LT PR : Nat → Nat) : Bool :=
  allN (nat_lit 120) (fun a => allN (nat_lit 120) (fun b =>
    bIf(Nat.beq a b, true, bIf(Nat.beq (CFSG.KC.O8.b8K false (nsK NS a) (nsK NS b)) (nat_lit 1),
      strictB (plK PR a b) (fun t => bAnd(Nat.blt t (nat_lit 1120), bAnd(onK LT t a,
        bAnd(onK LT t b, onK LT t (thirdK NS NI a b))))), true))))

@[expose] noncomputable def gensK (O G LT PR : Nat → Nat) : Bool :=
  allN (nat_lit 8) (fun i => allN (nat_lit 1120) (fun t => Nat.beq (pgW 11 (G i) t)
    (plK PR (pg 7 (nat_lit 127) (O i) (ltK LT 0 t)) (pg 7 (nat_lit 127) (O i) (ltK LT 1 t)))))

@[expose] noncomputable def onGK (O G LT : Nat → Nat) : Bool :=
  allN (nat_lit 8) (fun i => allN (nat_lit 1120) (fun t => strictB (pgW 11 (G i) t) (fun u =>
    bAnd(Nat.blt u (nat_lit 1120), bAnd(onK LT u (pg 7 (nat_lit 127) (O i) (ltK LT 0 t)),
    bAnd(onK LT u (pg 7 (nat_lit 127) (O i) (ltK LT 1 t)),
      onK LT u (pg 7 (nat_lit 127) (O i) (ltK LT 2 t))))))))

end CFSG.KC.AS81

end
