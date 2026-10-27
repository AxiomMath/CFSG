module

public import Certificates.Data.Kernel.SmithEKT

public section

namespace CFSG.SmithE.K

open CFSG.F4.Native

@[expose] noncomputable def pqStrict (y : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (f (nat_lit 0)) (fun n _ => f (Nat.succ n)) y

@[expose] noncomputable def pqApply : List Nat → Nat → Nat :=
  fun L => List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun x _ ih c => Nat.xor (Nat.mul (Nat.land c 1) x) (ih (Nat.shiftRight c 1))) L

@[expose] def pqKey (pr x y : Nat) : Nat := Nat.mod (Nat.add (Nat.mul x 1048576) y) pr

@[expose] def pqNot (B v : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight B v) 1) 0

@[expose] noncomputable def pqKeySet (pr : Nat) : List Nat → Nat → Nat → Nat :=
  fun P => List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => 0)
    (fun _ _ ih X Y => Nat.lor (Nat.shiftLeft 1 (pqKey pr (X % 1048576) (Y % 1048576)))
      (ih (X / 1048576) (Y / 1048576))) P

@[expose] noncomputable def pqPair (K1 K2 K3 K4 X4 X8 X10 X16 X6 X12 pl p k u0 u2 : Nat) : Bool :=
  pqNot K1 (pqKey 65521 u0 u2) || pqNot K2 (pqKey 65519 (fld k X4) (fld k X8)) ||
    pqNot K3 (pqKey 65497 (fld k X10) (fld k X16)) ||
    pqNot K4 (pqKey 65479 (fld k X6) (fld k X12)) || Nat.blt 0 (hermC p pl)

@[expose] def pqFld (k X : Nat) : Nat := Nat.land (Nat.shiftRight X (Nat.mul 20 k)) 1048575

@[expose] noncomputable def pqLane (K1 K2 K3 K4 X4 X8 X10 X16 X6 X12 pl l X0 X2 : Nat) :
    List Nat → Nat → Bool :=
  fun P => List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun p _ ih k => Nat.ble l k ||
      (pqPair K1 K2 K3 K4 X4 X8 X10 X16 X6 X12 pl p k (pqFld k X0) (pqFld k X2) &&
        pqStrict (Nat.succ k) ih)) P

@[expose] noncomputable def pqRow (C P : List Nat)
    (K1 K2 K3 K4 A0 A2 A4 A8 A10 A16 A6 A12 l pl : Nat) : Bool :=
  pqStrict (pqApply C (fld l A4)) fun X4 => pqStrict (pqApply C (fld l A8)) fun X8 =>
  pqStrict (pqApply C (fld l A10)) fun X10 => pqStrict (pqApply C (fld l A16)) fun X16 =>
  pqStrict (pqApply C (fld l A6)) fun X6 => pqStrict (pqApply C (fld l A12)) fun X12 =>
  pqStrict (pqApply C (fld l A0)) fun X0 => pqStrict (pqApply C (fld l A2)) fun X2 =>
  pqLane K1 K2 K3 K4 X4 X8 X10 X16 X6 X12 pl l X0 X2 P 0

@[expose] noncomputable def pqRows (C P : List Nat)
    (K1 K2 K3 K4 A0 A2 A4 A8 A10 A16 A6 A12 lo n : Nat) : List Nat → Nat → Bool :=
  fun Q => List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun pl _ ih r => (Nat.blt r lo || Nat.ble (lo + n) r ||
      pqRow C P K1 K2 K3 K4 A0 A2 A4 A8 A10 A16 A6 A12 r pl) && pqStrict (r + 1) ih) Q

@[expose] noncomputable def pqChk (C P : List Nat) (lo n : Nat) : Bool :=
  pqStrict (C.getD 0 0) fun A0 => pqStrict (C.getD 2 0) fun A2 =>
  pqStrict (C.getD 4 0) fun A4 => pqStrict (C.getD 8 0) fun A8 =>
  pqStrict (C.getD 10 0) fun A10 => pqStrict (C.getD 16 0) fun A16 =>
  pqStrict (C.getD 6 0) fun A6 => pqStrict (C.getD 12 0) fun A12 =>
  pqStrict (pqKeySet 65521 P A0 A2) fun K1 => pqStrict (pqKeySet 65519 P A4 A8) fun K2 =>
  pqStrict (pqKeySet 65497 P A10 A16) fun K3 => pqStrict (pqKeySet 65479 P A6 A12) fun K4 =>
  pqRows C P K1 K2 K3 K4 A0 A2 A4 A8 A10 A16 A6 A12 lo n P 0

end CFSG.SmithE.K
