module

public import Certificates.Data.Kernel.LeftOrb

public section

namespace CFSG.KC.E64CC

open CFSG.KC.Enum CFSG.KS
open CFSG.KLie.CT (fget)

@[expose] noncomputable def ap (p x : Nat) : Nat := pg (nat_lit 4) (nat_lit 15) p x

@[expose] noncomputable def eqK (p q : Nat) : Bool :=
  allN (nat_lit 14) fun i => Nat.beq (ap p i) (ap q i)

@[expose] noncomputable def idK (p : Nat) : Bool :=
  allN (nat_lit 14) fun i => Nat.beq (ap p i) i

@[expose] noncomputable def isPiK (p : Nat) : Bool :=
  allN (nat_lit 14) fun i => Nat.beq (ap p i) (Nat.mod (Nat.add i (nat_lit 7)) (nat_lit 14))

@[expose] noncomputable def commK (x g : Nat) : Bool :=
  allN (nat_lit 14) fun i => Nat.beq (ap x (ap g i)) (ap g (ap x i))

@[expose] noncomputable def cenK (x a b : Nat) : Bool := bAnd(commK x a, commK x b)

@[expose] noncomputable def eq3K (r p q : Nat) : Bool :=
  allN (nat_lit 14) fun i => Nat.beq (ap r i) (ap p (ap q i))

@[expose] noncomputable def mulK (p q : Nat) : Nat := pcomp (nat_lit 14) (nat_lit 4) (nat_lit 15) p q

@[expose] noncomputable def bitK (M i : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight M i) (nat_lit 1)) (nat_lit 1)

@[expose] noncomputable def mask3 (a b c : Nat) : Nat :=
  Nat.lor (Nat.lor (Nat.shiftLeft (nat_lit 1) a) (Nat.shiftLeft (nat_lit 1) b))
    (Nat.shiftLeft (nat_lit 1) c)

@[expose] noncomputable def orF (f : Nat → Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j acc => Nat.lor acc (Nat.shiftLeft (nat_lit 1) (f j))) n

@[expose] noncomputable def g6 (D : Nat → Nat) (st l : Nat) : Nat :=
  D (Nat.add (Nat.mul (nat_lit 2) (fget st (Nat.shiftRight l (nat_lit 1)) (nat_lit 4)))
    (Nat.land l (nat_lit 1)))

@[expose] noncomputable def evW (D : Nat → Nat) (st wd : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (pidn (nat_lit 14) (nat_lit 4))
    (fun i acc => mulK acc
      (g6 D st (Nat.mod (fget (Nat.shiftRight wd (nat_lit 8)) i (nat_lit 3)) (nat_lit 6))))
    (fget wd (nat_lit 0) (nat_lit 8))

@[expose] noncomputable def ixK (D T : Nat → Nat) (N k : Nat) : Bool :=
  strictB (D (Nat.add (nat_lit 28) k)) fun i => bAnd(Nat.blt i N, eqK (T i) (D k))

@[expose] noncomputable def piK (T : Nat → Nat) (N : Nat) : Bool :=
  allN N fun i => !isPiK (T i)

@[expose] noncomputable def cmK (D T : Nat → Nat) (N k : Nat) : Bool :=
  strictB (D (Nat.add (nat_lit 70) k)) fun cm =>
    strictB (D (Nat.mul (nat_lit 2) k)) fun a => strictB (D (Nat.add (Nat.mul (nat_lit 2) k) (nat_lit 1)))
      fun b => allN N fun i => bIf(cenK (T i) a b, bitK cm i, true)

@[expose] noncomputable def clK (D : Nat → Nat) (k : Nat) : Bool :=
  strictB (D (Nat.add (nat_lit 56) k)) fun cl =>
    Nat.beq (D (Nat.add (nat_lit 70) k)) (orF (fun j => fget cl j (nat_lit 14)) (nat_lit 32))

@[expose] noncomputable def setK (D : Nat → Nat) (s : Nat) : Bool :=
  strictB (D (Nat.add (nat_lit 84) s)) fun st =>
    strictB (fld(st, nat_lit 16, nat_lit 65535)) fun off => strictB (Nat.shiftRight st (nat_lit 32))
      fun sz => bAnd(idK (D (Nat.add (nat_lit 2450) off)),
        allN sz fun u => strictB (D (Nat.add (nat_lit 2450) (Nat.add off u))) fun x =>
          strictB (D (Nat.add (nat_lit 13538) (Nat.add off u))) fun e =>
            allN (nat_lit 6) fun l => strictB (fget e l (nat_lit 7)) fun v =>
              bAnd(Nat.blt v sz, eq3K (D (Nat.add (nat_lit 2450) (Nat.add off v))) (g6 D st l) x))

@[expose] noncomputable def outK (D : Nat → Nat) (st t : Nat) : Bool :=
  strictB (fld(st, nat_lit 16, nat_lit 65535)) fun off => strictB (Nat.shiftRight st (nat_lit 32))
    fun sz => bAnd(Nat.blt (nat_lit 0) sz,
      allN sz fun u => !eqK (D (Nat.add (nat_lit 2450) (Nat.add off u))) t)

@[expose] noncomputable def witK (D : Nat → Nat) (st t wx wy : Nat) : Bool :=
  strictB (evW D st wx) fun x => strictB (evW D st wy) fun y =>
    eqK (mulK t (mulK y x)) (mulK x y)

@[expose] noncomputable def resK (D T : Nat → Nat) (r : Nat) : Bool :=
  strictB (D (Nat.add (nat_lit 328) r)) fun rs =>
    strictB (D (Nat.add (nat_lit 84) (fld(rs, nat_lit 14, nat_lit 1023)))) fun st =>
      strictB (T (fget rs (nat_lit 0) (nat_lit 14))) fun t =>
        bIf(Nat.beq (Nat.shiftRight rs (nat_lit 24)) (nat_lit 0),
          witK D st t (D (Nat.add (nat_lit 1035) r)) (D (Nat.add (nat_lit 1742) r)), outK D st t)

@[expose] noncomputable def setIs (st k₁ k₂ k₃ : Nat) : Bool :=
  Nat.beq (mask3 (fget st (nat_lit 0) (nat_lit 4)) (fget st (nat_lit 1) (nat_lit 4))
    (fget st (nat_lit 2) (nat_lit 4))) (mask3 k₁ k₂ k₃)

@[expose] noncomputable def tripK (D : Nat → Nat) (k₁ k₂ k₃ : Nat) : Bool :=
  strictB (D (Nat.add (nat_lit 24626) (Nat.add (Nat.mul (nat_lit 196) k₁)
    (Nat.add (Nat.mul (nat_lit 14) k₂) k₃)))) fun tr =>
  strictB (D (Nat.add (nat_lit 56) k₁)) fun cl =>
  strictB (D (Nat.add (nat_lit 70) k₂)) fun m₂ => strictB (D (Nat.add (nat_lit 70) k₃)) fun m₃ =>
    allN (nat_lit 32) fun j => strictB (fget cl j (nat_lit 14)) fun c =>
      bIf(bAnd(!Nat.beq c (nat_lit 0), bAnd(bitK m₂ c, bitK m₃ c)),
        strictB (fget tr j (nat_lit 12)) fun r =>
          bAnd(!Nat.beq r (nat_lit 0), bAnd(Nat.blt r (nat_lit 708),
            strictB (D (Nat.add (nat_lit 328) r)) fun rs =>
              bAnd(Nat.beq (fget rs (nat_lit 0) (nat_lit 14)) c,
                bAnd(Nat.blt (fld(rs, nat_lit 14, nat_lit 1023)) (nat_lit 245),
                  setIs (D (Nat.add (nat_lit 84) (fld(rs, nat_lit 14, nat_lit 1023)))) k₁ k₂ k₃)))),
        true)

end CFSG.KC.E64CC

end
