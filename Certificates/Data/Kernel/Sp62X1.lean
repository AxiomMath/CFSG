module

public import Certificates.Data.Kernel.Sp62Pk

public section

namespace CFSG.KD.Sp62X1

open CFSG.KD.Sp62

@[expose] noncomputable def commN (x y : Nat) : Bool := Nat.beq (MULF x y) (MULF y x)

@[expose] noncomputable def invN (x : Nat) : Bool := Nat.beq (MULF x x) ONE && !Nat.beq x ONE

@[expose] noncomputable def memN (x : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ r => Nat.beq x a || r) L

@[expose] noncomputable def eraseN (x : Nat) (L : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun a l r =>
    Bool.rec (motive := fun _ => List Nat) (a :: r) l (Nat.beq a x)) L

@[expose] noncomputable def cntN (v : Nat) (R : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun w _ r =>
    Bool.rec (motive := fun _ => Nat) r (Nat.succ r) (!Nat.beq w v && commN v w)) R

@[expose] noncomputable def peelN (d : Nat) (R P : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun v _ r R => memN v R && Nat.blt (cntN v R) d && r (eraseN v R)) P R

@[expose] noncomputable def resN (R P : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun R => R)
    (fun v _ r R => r (eraseN v R)) P R

@[expose] noncomputable def allL (f : Nat → Bool) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ r => f a && r) L

end CFSG.KD.Sp62X1

end
