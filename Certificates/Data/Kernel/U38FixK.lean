module

public import Certificates.Data.Kernel.U38QK

public section

namespace CFSG.KC.U38FixK

open CFSG.KC.Enum CFSG.KS CFSG.KC.U38QK

@[expose] noncomputable def commK (n w a b : Nat) : Bool :=
  Nat.beq (pcomp n w (mask w) a b) (pcomp n w (mask w) b a)

@[expose] noncomputable def fixRowK (n w x : Nat) (s : Nat → Bool) (a : Nat) : Bool :=
  !(cubeK n w a && commK n w a x) || s a

@[expose] noncomputable def pw3K (n w x a : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) (pcomp n w (mask w) x x) x (Nat.beq a 1))
    (pidn n w) (Nat.beq a 0)

@[expose] noncomputable def memK (y : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun x _ ih => Nat.beq x y || ih) L

@[expose] noncomputable def conjEqK (n w u z e : Nat) : Bool :=
  Nat.beq (pcomp n w (mask w) u z) (pcomp n w (mask w) e u)

@[expose] noncomputable def coverRowK (n w : Nat) (T H E : Nat → Nat) (XI : List Nat) (z c : Nat) :
    Bool :=
  !cubeK n w (T z) || Nat.beq (T z) (pidn n w) ||
    (memK (c / 36) XI &&
      conjEqK n w (pcomp n w (mask w) (H (c % 4)) (T (c / 36))) (T z) (E (c / 4 % 9)))

end CFSG.KC.U38FixK

end
