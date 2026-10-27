module

public import Certificates.Data.Kernel.Spor.Text

public section

namespace CFSG.KC.DecText

@[expose] noncomputable def digitsOK (cs : List Char) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun ch _ ih => (Nat.beq (Char.toNat ch) 32 || (Nat.ble 48 (Char.toNat ch) &&
      Nat.ble (Char.toNat ch) 57)) && ih) cs

@[expose] noncomputable def natsRun (cs : List Char) : Nat → Bool → List Nat :=
  List.rec (motive := fun _ => Nat → Bool → List Nat)
    (fun cur st => Bool.rec (motive := fun _ => List Nat) [] [cur] st)
    (fun ch _ ih cur st =>
      Bool.rec (motive := fun _ => List Nat)
        (ih (Nat.add (Nat.mul cur 10) (Nat.sub (Char.toNat ch) 48)) true)
        (Bool.rec (motive := fun _ => List Nat) (ih 0 false) (List.cons cur (ih 0 false)) st)
        (Nat.beq (Char.toNat ch) 32))
    cs

@[expose] noncomputable def natsK (cs : List Char) : List Nat := natsRun cs 0 false

end CFSG.KC.DecText

end
