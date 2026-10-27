module

public import Certificates.Data.Kernel.Misc.T46

public section

namespace CFSG.KC.MiscCoset.T46W

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc CFSG.KC.Misc.O73 CFSG.KC.Misc.T46

@[expose] noncomputable def walkT (A : Nat → Nat) (w : List Int) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun z _ ih x => A (Nat.add (Nat.mul (ih x) 46) (Nat.sub (Int.natAbs z) 1))) w x

@[expose] noncomputable def lettersK (rws : List (List Int)) (xw xp yw yp : List Int) : Bool :=
  andB (List.rec (motive := fun _ => Bool) true (fun w _ ih => andB (lettersOK 46 w) ih) rws) <|
  andB (andB (lettersOK 46 xw) (lettersOK 46 xp)) (andB (lettersOK 46 yw) (lettersOK 46 yp))

@[expose] noncomputable def pointK (A : Nat → Nat) (GP : List Nat) (rws : List (List Int))
    (xw xp yw yp : List Int) (x : Nat) : Bool :=
  andB (allN 46 fun k => Nat.beq (A (Nat.add (Nat.mul x 46) k)) (at' 10 (wordM7.nthN GP k) x)) <|
  andB (List.rec (motive := fun _ => Bool) true
    (fun w _ ih => andB (Nat.beq (walkT A w x) x) ih) rws) <|
  andB (Nat.beq (walkT A xw x) (walkT A xp (walkT A xp (walkT A xp x)))) <|
  andB (Nat.beq (walkT A yw x) (walkT A yp (walkT A yp x))) <|
    allN 46 fun k => Nat.beq (A (Nat.add (Nat.mul (A (Nat.add (Nat.mul x 46) k)) 46) k)) x

end CFSG.KC.MiscCoset.T46W

end
