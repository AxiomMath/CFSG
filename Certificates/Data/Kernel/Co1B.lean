module

public import Certificates.Data.Kernel.Co1F2

public section

namespace CFSG.KC.Co1B

open CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KLie.CT

@[expose] noncomputable def oneK : Nat := idF (nat_lit 24)

@[expose] noncomputable def mulK (A B : Nat) : Nat := mulF (nat_lit 24) A B

@[expose] noncomputable def eqK (A B : Nat) : Bool :=
  Nat.beq (Nat.mod A (Nat.shiftLeft (nat_lit 1) (nat_lit 576))) (Nat.mod B (Nat.shiftLeft (nat_lit 1) (nat_lit 576)))

@[expose] noncomputable def canK (A : Nat) : Bool := Nat.blt A (Nat.shiftLeft (nat_lit 1) (nat_lit 576))

@[expose] noncomputable def letK (rs is : List Nat) (j : Int) : Nat :=
  Int.rec (motive := fun _ => Nat)
    (fun n => Nat.rec (motive := fun _ => Nat) (getL oneK is (nat_lit 0)) (fun k _ => getL oneK rs k) n)
    (fun n => getL oneK is n) j

@[expose] noncomputable def wordFromK (rs is : List Nat) (w : List Int) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun j _ ih acc => strictN (mulK acc (letK rs is j)) ih) w

@[expose] noncomputable def wordK (rs is : List Nat) (w : List Int) : Nat := wordFromK rs is w oneK

@[expose] noncomputable def takeK (n : Nat) (l : List Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun x _ ih n => Nat.rec (motive := fun _ => List Nat) List.nil (fun k _ => List.cons x (ih k)) n) l n

@[expose] noncomputable def prefixK (p : List Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun x _ ih l => List.rec (motive := fun _ => Bool) false (fun y t _ => andB (Nat.beq x y) (ih t)) l) p

@[expose] noncomputable def invsK (RS : List Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun l => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) l)
    (fun m _ ih l => List.rec (motive := fun _ => Bool) false
      (fun mi t _ => andB (andB (canK m) (canK mi)) (andB (Nat.beq (mulK m mi) oneK) (ih t))) l) RS

@[expose] noncomputable def stepsK (RS RIS : List Nat) (derivs : List (List Int)) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun k => Nat.beq (lenL RS) k)
    (fun w _ ih k => andB (Nat.beq (getL oneK RS k) (wordK (takeK k RS) (takeK k RIS) w)) (ih (Nat.succ k)))
    derivs

@[expose] noncomputable def dagOK (base : List Nat) (derivs : List (List Int)) (RS RIS : List Nat) : Bool :=
  andB (prefixK base RS) (andB (invsK RS RIS) (stepsK RS RIS derivs (lenL base)))

@[expose] noncomputable def pget (P i : Nat) : Nat :=
  Nat.land (Nat.shiftRight P (Nat.mul (nat_lit 8) i)) (nat_lit 255)

@[expose] noncomputable def ppack (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft (f i) (Nat.mul (nat_lit 8) i))) (nat_lit 240)

@[expose] noncomputable def pcomp (t u : Nat) : Nat := strictN t fun t => strictN u fun u => ppack fun i => pget t (pget u i)

@[expose] noncomputable def pidK : Nat := ppack fun i => i

@[expose] noncomputable def pword (R : List Nat) (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) pidK (fun r _ ih => pcomp (getL (nat_lit 0) R r) ih) l

end CFSG.KC.Co1B

end
