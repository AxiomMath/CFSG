module

public import Certificates.Data.Kernel.HMathieu.FixCert

public section

namespace CFSG.KC.HMathieu

open CFSG.Quasithin.H.Mathieu

@[expose] def incB : List Nat → Bool
  | a :: b :: l => decide (a < b) && incB (b :: l)
  | _ => true

@[expose] noncomputable def actK (cs : List Nat) (m : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun c _ ih m => Nat.xor (bif Nat.beq (Nat.land m 1) 1 then c else 0)
      (ih (Nat.shiftRight m 1))) cs m

@[expose] noncomputable def fixRowOK (n : Nat) (M F J : List Nat) : Bool :=
  F.all (fun x => decide (x < 2 ^ n) && Nat.beq (actK M x) x) && incB F &&
    J.all (fun j => decide (j < n)) && imgOK M J && F.length == 2 ^ (n - J.length)

@[expose] noncomputable def fixTabOK (n : Nat) :
    List (List Nat) → List (List Nat) → List (List Nat) → Bool
  | [], [], [] => true
  | M :: Ms, F :: Fs, J :: Js => fixRowOK n M F J && fixTabOK n Ms Fs Js
  | _, _, _ => false

end CFSG.KC.HMathieu

end
