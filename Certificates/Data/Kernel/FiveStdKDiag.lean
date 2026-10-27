module

public import Certificates.Data.Kernel.FiveStdKSyl

public section

namespace CFSG.KC.FiveStdK

@[expose] noncomputable def orB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) b true a

@[expose] noncomputable def anyN (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun i ih => orB (f i) ih) n

@[expose] noncomputable def zK : Nat := 79254

@[expose] noncomputable def memA (A nA c : Nat) : Bool := anyN nA fun i => Nat.beq (f20 A i) c

@[expose] noncomputable def inKKK (a : Nat) : Bool :=
  andB (Nat.beq (fS a) 0) <|
    Nat.beq (Nat.mod (Nat.add (Nat.mul (fA0 a) (fA3 a)) (Nat.mul 4 (Nat.mul (fA1 a) (fA2 a)))) 5)
      (Nat.mod (Nat.add (Nat.mul (fB0 a) (fB3 a)) (Nat.mul 4 (Nat.mul (fB1 a) (fB2 a)))) 5)

@[expose] noncomputable def dAPt (A nA g i : Nat) : Bool :=
  letB (f20 A i) fun a =>
    andB (ifB (Nat.blt (Nat.succ i) nA) (Nat.blt a (f20 A (Nat.succ i))) true) <|
    andB (validK a) <| andB (Nat.beq (mulK a g) (mulK g a)) <| andB (Nat.beq (powK a 5) oneK) <|
    andB (inKKK a) <| allN nA fun j => memA A nA (mulK a (f20 A j))

@[expose] noncomputable def dBPt (A nA B v0 k : Nat) : Bool :=
  letB (f20 B k) fun b => letB (invK b) fun bi =>
    andB (ifB (Nat.beq (powK b 5) oneK) (memA A nA b) true) <|
    andB (allN nA fun j => memA A nA (cjK b bi (f20 A j))) <|
      letB (mulK v0 b) fun v => letB (invK v) fun vi =>
        ifB (Nat.beq (fS v) 0) (allN nA fun j => letB (f20 A j) fun a => Nat.beq (cjK v vi a) (invK a)) true

@[expose] noncomputable def dgOK (A nA B Mc g v0 : Nat) : Bool :=
  andB (allN nA (dAPt A nA g)) (allN Mc (dBPt A nA B v0))

@[expose] noncomputable def nvPt (B k : Nat) : Bool :=
  letB (f20 B k) fun b => ifB (Nat.beq (mulK b b) oneK) (orB (Nat.beq b oneK) (Nat.beq b zK)) true

@[expose] noncomputable def noInvK (B Mc : Nat) : Bool := allN Mc (nvPt B)

end CFSG.KC.FiveStdK

end
