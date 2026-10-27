module

public import Certificates.Data.Kernel.ChengHeldPropsK

public section

namespace CFSG.KC.ChengHeldP

open CFSG.OddStandard.ChengHeldData CFSG.KC.ChengHeldS2
open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw

@[expose] noncomputable def bitM (B x : ℕ) : Bool := Nat.blt 0 (Nat.land B (Nat.shiftLeft 1 x))

@[expose] noncomputable def subM (A B : ℕ) : Bool := Nat.beq (Nat.land A B) A

@[expose] noncomputable def bEqv (p q : Bool) : Bool := Bool.rec (Bool.not q) q p

@[expose] noncomputable def eaInvW (n w : ℕ) (T : ℕ → ℕ) (IXP AP RK cI : ℕ) : Bool :=
  bAnd(allN cI fun t => strictB (pg w (mask w) AP t) fun a =>
      bAnd(Nat.blt a n, bAnd(Bool.not (Nat.beq a 0),
        Nat.beq (pg w (mask w) (T (pg w (mask w) IXP a)) a) 0)),
    allN n fun x => strictB (pg w (mask w) RK x) fun r =>
      bIf(bAnd(Bool.not (Nat.beq x 0), Nat.beq (pg w (mask w) (T (pg w (mask w) IXP x)) x) 0),
        bAnd(Nat.blt r cI, Nat.beq (pg w (mask w) AP r) x), true))

@[expose] noncomputable def eaCMW (n w : ℕ) (T : ℕ → ℕ) (IXP IVP AP CMP cI : ℕ) : Bool :=
  allN cI fun t => strictB (pg w (mask w) AP t) fun a =>
    strictB (T (pg w (mask w) IXP a)) fun R => strictB (pg n (mask n) CMP t) fun C =>
      allN n fun x => bEqv (bitM C x)
        (Nat.beq (pg w (mask w) R x) (iW n w IVP (pg w (mask w) R (iW n w IVP x))))

@[expose] noncomputable def eaL1W (n w AP L1 cI : ℕ) : Bool :=
  bAnd(allN cI fun t =>
      Nat.beq (pg n (mask n) L1 t) (Nat.lor 1 (Nat.shiftLeft 1 (pg w (mask w) AP t))),
    allN (Nat.sub cI 1) fun t => Nat.blt (pg n (mask n) L1 t) (pg n (mask n) L1 (Nat.succ t)))

@[expose] noncomputable def eaUpW (n w : ℕ) (T : ℕ → ℕ) (IXP AP CMP cI L0 c0 L1 c1 PJ PT : ℕ) :
    Bool :=
  bAnd(allN c1 fun i => strictB (pg 10 (mask 10) PJ i) fun j =>
      strictB (pg 10 (mask 10) PT i) fun t => strictB (pg w (mask w) AP t) fun a =>
      strictB (pg n (mask n) L0 j) fun E => strictB (pg n (mask n) L1 i) fun F =>
      strictB (T (pg w (mask w) IXP a)) fun R =>
        bAnd(Nat.blt j c0, bAnd(Nat.blt t cI, bAnd(Bool.not (bitM E a),
          bAnd(subM E (pg n (mask n) CMP t),
            allN n fun y => bEqv (bitM F y) (Bool.or (bitM E y) (bitM E (pg w (mask w) R y))))))),
    allN (Nat.sub c1 1) fun i => Nat.blt (pg n (mask n) L1 i) (pg n (mask n) L1 (Nat.succ i)))

@[expose] noncomputable def eaWitW (n w AP CMP cI L0 c0 L1 c1 : ℕ) (W : ℕ → ℕ) (b : ℕ) : Bool :=
  allN c0 fun j => strictB (pg n (mask n) L0 j) fun E => strictB (W (Nat.add b j)) fun V =>
    allN cI fun t => strictB (pg w (mask w) AP t) fun a =>
      bIf(bAnd(Bool.not (bitM E a), subM E (pg n (mask n) CMP t)),
        strictB (pg 10 (mask 10) V t) fun i => bAnd(Nat.blt i c1,
          strictB (pg n (mask n) L1 i) fun F => bAnd(subM E F, bitM F a)),
        true)

end CFSG.KC.ChengHeldP

end
