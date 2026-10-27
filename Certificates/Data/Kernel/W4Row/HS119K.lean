module

public import Certificates.Data.Kernel.Misc.PermClos

public section

namespace CFSG.KC.HS119

open CFSG.KC.Ord CFSG.KC.LQT.P

@[expose] noncomputable def letN (y : Nat) (k : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (k (nat_lit 0)) (fun m _ => k (Nat.succ m)) y

@[expose] noncomputable def fd (w x i : Nat) : Nat :=
  Nat.land (Nat.shiftRight x (Nat.mul w i)) (Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1))

@[expose] noncomputable def bitB (x i : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight x i) (nat_lit 1)) (nat_lit 1)

@[expose] noncomputable def eqB (x y : Bool) : Bool := Bool.rec (motive := fun _ => Bool) (notB y) y x

@[expose] noncomputable def invAt (E IX II : Nat → Nat) (k : Nat) : Bool :=
  letB (IX k) fun a => andB (Nat.blt a (nat_lit 256))
    (eqB (Nat.beq (mul (nat_lit 32) (E k) (E k)) (E (nat_lit 0)))
      (andB (Nat.blt a (nat_lit 192)) (Nat.beq (II a) k)))

@[expose] noncomputable def iiAt (IX II : Nat → Nat) (a : Nat) : Bool :=
  letB (II a) fun k => andB (Nat.blt k (nat_lit 1024)) (Nat.beq (IX k) a)

@[expose] noncomputable def pairAt (E II PT : Nat → Nat) (a b : Nat) : Bool :=
  impB (Nat.blt a b) (letB (fd (nat_lit 16) (PT a) b) fun m => andB (Nat.blt m (nat_lit 1024))
    (Nat.beq (mul (nat_lit 32) (E (II a)) (E (II b))) (E m)))

@[expose] noncomputable def pxK (PT IX : Nat → Nat) (a b : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (IX (fd (nat_lit 16) (PT b) a)) (Nat.blt b a))
    (IX (fd (nat_lit 16) (PT a) b)) (Nat.blt a b)

@[expose] noncomputable def cmAt (PT IX CM : Nat → Nat) (a b : Nat) : Bool :=
  eqB (bitB (CM a) b) (Nat.blt (pxK PT IX a b) (nat_lit 192))

@[expose] noncomputable def cgAt (E II G CG : Nat → Nat) (l a : Nat) : Bool :=
  letB (fd (nat_lit 8) (CG l) a) fun b => andB (Nat.blt b (nat_lit 192))
    (Nat.beq (conj (nat_lit 32) (G l) (E (II a))) (E (II b)))

@[expose] noncomputable def rhoAt (H Om G : Nat → Nat) (l i : Nat) : Bool :=
  Nat.beq (fd (nat_lit 12) (H l) (Om i)) (Om (img (G l) i))

@[expose] noncomputable def omAt (Om : Nat → Nat) (i : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) (Nat.blt (Om i) (nat_lit 3850))
    (Nat.blt (Om i) (Om (Nat.succ i))) (Nat.blt i (nat_lit 31))

@[expose] noncomputable def parK (PA : Nat → Nat) (gout : Nat) (fuel : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 2)
    (fun _ ih k => Bool.rec (motive := fun _ => Nat)
      (letN (PA k) fun r => Nat.xor (ih (Nat.land r (nat_lit 16777215)))
        (Nat.land (Nat.shiftRight gout (Nat.shiftRight r (nat_lit 24))) (nat_lit 1)))
      (nat_lit 0) (Nat.beq k (nat_lit 0))) fuel

@[expose] noncomputable def conjP (PA CG : Nat → Nat) (fuel : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => nat_lit 255)
    (fun _ ih c a => Bool.rec (motive := fun _ => Nat)
      (letN (PA c) fun r => ih (Nat.land r (nat_lit 16777215))
        (fd (nat_lit 8) (CG (Nat.shiftRight r (nat_lit 24))) a))
      a (Nat.beq c (nat_lit 0))) fuel

@[expose] noncomputable def lMask (L : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft (nat_lit 1) (fd (nat_lit 8) L (Nat.succ i))))
    (fd (nat_lit 8) L (nat_lit 0))

@[expose] noncomputable def lsAt (R L : Nat → Nat) (j : Nat) : Bool := Nat.beq (lMask (L j)) (R j)

@[expose] noncomputable def cMask (PA CG PT IX : Nat → Nat) (c t L : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => letN (fd (nat_lit 8) L (Nat.succ i)) fun x =>
      Nat.lor (Nat.lor acc (Nat.shiftLeft (nat_lit 1) (conjP PA CG (nat_lit 9) c x)))
        (Nat.shiftLeft (nat_lit 1) (conjP PA CG (nat_lit 9) c (pxK PT IX t x))))
    (fd (nat_lit 8) L (nat_lit 0))

@[expose] noncomputable def extAt (inner : Bool) (PA : Nat → Nat) (gout : Nat)
    (II PT IX CM CG R L XS : Nat → Nat) (nR j t : Nat) : Bool :=
  letB (R j) fun X =>
    impB (andB (notB (bitB X t)) (andB (Nat.beq (Nat.land X (CM t)) X)
        (impB inner (Nat.beq (parK PA gout (nat_lit 9) (II t)) (nat_lit 0)))))
      (letB (fd (nat_lit 32) (XS j) t) fun e => letB (Nat.land e (nat_lit 1023)) fun c =>
        letB (Nat.shiftRight e (nat_lit 10)) fun j₁ =>
          andB (Nat.blt j₁ nR) (andB (impB inner (Nat.beq (parK PA gout (nat_lit 9) c) (nat_lit 0)))
            (Nat.beq (cMask PA CG PT IX c t (L j)) (R j₁))))

end CFSG.KC.HS119

end
