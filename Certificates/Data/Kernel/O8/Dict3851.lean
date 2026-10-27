module

public import CFSG.Certificates.Kernel.Lie.CT.Core

public section

namespace CFSG.KC.O8D

open CFSG.KLie.CT

@[expose] noncomputable def pbK (v : Nat) : Nat :=
  Nat.lor (Nat.lor (Nat.land v (nat_lit 23))
    (Nat.shiftLeft (Nat.land (Nat.shiftRight v (nat_lit 3)) (nat_lit 1)) (nat_lit 5)))
    (Nat.shiftLeft (Nat.land (Nat.shiftRight v (nat_lit 5)) (nat_lit 1)) (nat_lit 3))

@[expose] noncomputable def jsK (v : Nat) : Nat :=
  Nat.lor (Nat.shiftLeft (Nat.land v (nat_lit 7)) (nat_lit 3))
    (Nat.land (Nat.shiftRight v (nat_lit 3)) (nat_lit 7))

@[expose] noncomputable def kcK (w x : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (jsK (pbK (Nat.land x (nat_lit 63))))
    (Nat.add (Nat.xor (jsK (pbK (Nat.land x (nat_lit 63)))) w) (nat_lit 64)) (bit x (nat_lit 6))

@[expose] noncomputable def kiK (w e : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (pbK (jsK (Nat.land e (nat_lit 63))))
    (Nat.add (pbK (jsK (Nat.xor (Nat.land e (nat_lit 63)) w))) (nat_lit 64)) (bit e (nat_lit 6))

@[expose] noncomputable def phiK (A : Nat → Nat → Nat) (w i v : Nat) : Nat :=
  Nat.land (kiK w (A i (kcK w (Nat.add v (nat_lit 64))))) (nat_lit 63)

@[expose] noncomputable def actPhiK (A : Nat → Nat → Nat) (w i x : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Nat.xor (phiK A w i (Nat.land x (nat_lit 63))) (phiK A w i (nat_lit 0)))
    (Nat.add (phiK A w i (Nat.land x (nat_lit 63))) (nat_lit 64)) (bit x (nat_lit 6))

@[expose] noncomputable def beqB (a b : Bool) : Bool := Bool.rec (notB b) b a

@[expose] noncomputable def kapAt (w x : Nat) : Bool :=
  andB (Nat.blt (kcK w x) (nat_lit 128)) (andB (Nat.beq (kiK w (kcK w x)) x)
    (andB (Nat.blt (kiK w x) (nat_lit 128)) (andB (Nat.beq (kcK w (kiK w x)) x)
      (allN (nat_lit 128) fun y => Nat.beq (kcK w (Nat.xor x y)) (Nat.xor (kcK w x) (kcK w y))))))

@[expose] noncomputable def phiAt (A : Nat → Nat → Nat) (G : Nat → Nat) (w Q i v : Nat) : Bool :=
  andB (beqB (bit Q (phiK A w i v)) (bit Q v)) (andB
    (Nat.beq (phiK A w (G i) (phiK A w i v)) v) (Nat.beq (phiK A w i (phiK A w (G i) v)) v))

@[expose] noncomputable def actAt (A : Nat → Nat → Nat) (w i x : Nat) : Bool :=
  Nat.beq (kiK w (A i (kcK w x))) (actPhiK A w i x)

@[expose] noncomputable def movAt (A : Nat → Nat → Nat) (i : Nat) : Bool :=
  orB (Nat.beq i (nat_lit 0)) (anyN (nat_lit 128) fun e => notB (Nat.beq (A i e) e))

@[expose] noncomputable def orbMask (A : Nat → Nat → Nat) (w v : Nat) : Nat :=
  orN (nat_lit 512) fun i => pw2 (A i (kcK w (Nat.add v (nat_lit 64))))

@[expose] noncomputable def orbAt (A : Nat → Nat → Nat) (w Q t v : Nat) : Bool :=
  orB (bit Q v) (orB (notB (Nat.beq (popc (nat_lit 128) (orbMask A w v)) (nat_lit 4)))
    (bit (orbMask A w v) t))

end CFSG.KC.O8D

end
