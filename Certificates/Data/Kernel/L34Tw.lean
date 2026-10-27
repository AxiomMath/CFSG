module

public import Certificates.Data.Kernel.Spor.Chain
public import CFSG.Certificates.Kernel.Lie.CT.Core

public section

namespace CFSG.KC.L34Tw

open CFSG.KC.Enum CFSG.KS
open CFSG.KLie.CT (andB orB notB)

@[expose] noncomputable def mulK (p q : Nat) : Nat := pcomp 42 6 (mask 6) p q

@[expose] noncomputable def idK : Nat := pidn 42 6

@[expose] noncomputable def commK (p q : Nat) : Bool := Nat.beq (mulK p q) (mulK q p)

@[expose] noncomputable def inv2K (p : Nat) : Bool := Nat.beq (mulK p p) idK

@[expose] noncomputable def memT (T : Nat → Nat) (x : Nat) : Bool :=
  notB (allN 64 fun q => notB (Nat.beq (T q) x))

@[expose] noncomputable def cntN (n : Nat) (f : Nat → Bool) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun i ih => nIf(f i, Nat.succ ih, ih)) n

@[expose] noncomputable def normK (T G : Nat → Nat) (h₅ h₆ : Nat) : Bool :=
  andB (inv2K h₅) (andB (inv2K h₆) (andB (commK h₅ h₆) (allN 4 fun i =>
    andB (memT T (mulK (mulK h₅ (G i)) h₅)) (memT T (mulK (mulK h₆ (G i)) h₆)))))

@[expose] noncomputable def kleinK (T : Nat → Nat) (s r : Nat) : Bool :=
  andB (Nat.blt r (nat_lit 4096)) <|
  strictB (T (Nat.land r (nat_lit 63))) fun a => strictB (T (Nat.shiftRight r (nat_lit 6))) fun b =>
    andB (inv2K a) (andB (inv2K b) (andB (notB (Nat.beq a idK)) (andB (notB (Nat.beq b idK))
      (andB (notB (Nat.beq a b)) (andB (commK a b) (andB (commK a s) (commK b s)))))))

@[expose] noncomputable def kleinAllK (T : Nat → Nat) (h₅ h₆ : Nat) (W : Nat → Nat) : Bool :=
  allN 128 fun k => strictB (mulK (nIf(Nat.blt k (nat_lit 64), h₅, h₆)) (T (Nat.land k (nat_lit 63))))
    fun s => orB (notB (inv2K s)) (kleinK T s (W k))

@[expose] noncomputable def tK (T : Nat → Nat) (h₅ h₆ q₀ : Nat) : Bool :=
  andB (Nat.blt q₀ (nat_lit 64)) <| strictB (mulK h₅ (T q₀)) fun t =>
    andB (inv2K t) (andB (commK h₅ t) (andB (commK (mulK h₅ h₆) t) (notB (Nat.beq t h₅))))

@[expose] noncomputable def centK (G : Nat → Nat) (h₅ h₆ z : Nat) : Bool :=
  andB (inv2K z) (andB (notB (Nat.beq z idK)) (andB (commK z h₅) (andB (commK z h₆)
    (allN 4 fun i => commK z (G i)))))

@[expose] noncomputable def uniK (T : Nat → Nat) (r : Nat) (U : Nat → Nat) : Bool :=
  allN 64 fun q => strictB (mulK (T q) r) fun x =>
    orB (notB (inv2K x)) (andB (Nat.blt (U q) (nat_lit 64))
      (strictB (T (U q)) fun c => Nat.beq (mulK x c) (mulK c r)))

@[expose] noncomputable def bigK (T : Nat → Nat) (b : Nat) : Bool :=
  allN 64 fun a => strictB (T a) fun t =>
    orB (notB (inv2K t)) (Nat.ble b (cntN 64 fun q => strictB (T q) fun y => commK t y))

@[expose] noncomputable def cosK (T : Nat → Nat) (r i q : Nat) : Nat :=
  nIf(Nat.beq i (nat_lit 0), T q, mulK (T q) r)

@[expose] noncomputable def sumN (n : Nat) (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun i ih => Nat.add (f i) ih) n

@[expose] noncomputable def tally (inside sq ok : Bool) : Nat :=
  nIf(inside, Nat.add (nat_lit 1) (Nat.add (nIf(sq, nat_lit 256, nat_lit 0))
    (nIf(ok, nat_lit 0, nat_lit 65536))), nat_lit 0)

@[expose] noncomputable def tallyOK (s q j : Nat) : Bool :=
  andB (Nat.ble (Nat.land s (nat_lit 255)) q)
    (andB (Nat.ble (Nat.land (Nat.shiftRight s (nat_lit 8)) (nat_lit 255)) j)
      (Nat.beq (Nat.shiftRight s (nat_lit 16)) (nat_lit 0)))

@[expose] noncomputable def tallyC (T : Nat → Nat) (r t u i : Nat) (ok : Nat → Bool) (q : Nat) :
    Nat :=
  strictN (cosK T r i q) fun y => nIf(andB (commK y t) (commK y u),
    strictN (mulK y y) fun A => tally true (Nat.beq A idK) (ok A), nat_lit 0)

@[expose] noncomputable def qK (T : Nat → Nat) (r : Nat) (Q I : Nat → Nat) (v : Nat) : Bool :=
  allN 2 fun i => tallyOK (sumN 64 (tallyC T r v v i inv2K)) (Q i) (I i)

@[expose] noncomputable def qAllK (T : Nat → Nat) (r : Nat) (Q I : Nat → Nat) : Bool :=
  allN 64 fun c => strictB (mulK (T c) r) fun v => orB (notB (inv2K v)) (qK T r Q I v)

@[expose] noncomputable def pSum (T : Nat → Nat) (r t u i : Nat) : Nat :=
  sumN 64 (tallyC T r t u i fun A => orB (Nat.beq A idK) (Nat.beq A t))

@[expose] noncomputable def pK (T : Nat → Nat) (r : Nat) (Q I : Nat → Nat) (t u : Nat) : Bool :=
  strictB (pSum T r t u 0) fun s₀ => strictB (pSum T r t u 1) fun s₁ =>
    andB (tallyOK s₀ 255 255) (andB (tallyOK s₁ 255 255)
      (andB (Nat.ble (Nat.add (Nat.mul (Nat.land s₀ (nat_lit 255)) (Q 0))
          (Nat.mul (Nat.land s₁ (nat_lit 255)) (Q 1))) (nat_lit 128))
        (Nat.blt (Nat.add (Nat.mul (Nat.land (Nat.shiftRight s₀ (nat_lit 8)) (nat_lit 255)) (I 0))
          (Nat.mul (Nat.land (Nat.shiftRight s₁ (nat_lit 8)) (nat_lit 255)) (I 1))) (nat_lit 16))))

@[expose] noncomputable def pAllK (T : Nat → Nat) (r : Nat) (Q I : Nat → Nat) : Bool :=
  allN 64 fun b => strictB (mulK (T b) r) fun u => orB (notB (inv2K u))
    (allN 64 fun a => strictB (T a) fun t =>
      orB (notB (andB (inv2K t) (andB (notB (Nat.beq t idK)) (commK t u)))) (pK T r Q I t u))

end CFSG.KC.L34Tw

end
