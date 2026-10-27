module

public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KS.DecSL

@[expose] noncomputable def isSep (c : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) (Nat.beq c (nat_lit 10)) true (Nat.beq c (nat_lit 32))

@[expose] noncomputable def digitsSLOK (cs : List Char) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun ch _ ih => bAnd(Bool.rec (motive := fun _ => Bool)
      (bAnd(Nat.ble (nat_lit 48) (Char.toNat ch), Nat.ble (Char.toNat ch) (nat_lit 57))) true
      (isSep (Char.toNat ch)), ih)) cs

@[expose] noncomputable def natsRun (cs : List Char) : Nat → Bool → List Nat :=
  List.rec (motive := fun _ => Nat → Bool → List Nat)
    (fun cur st => Bool.rec (motive := fun _ => List Nat) [] [cur] st)
    (fun ch _ ih cur st =>
      Bool.rec (motive := fun _ => List Nat)
        (ih (Nat.add (Nat.mul cur (nat_lit 10)) (Nat.sub (Char.toNat ch) (nat_lit 48))) true)
        (Bool.rec (motive := fun _ => List Nat) (ih (nat_lit 0) false)
          (List.cons cur (ih (nat_lit 0) false)) st)
        (isSep (Char.toNat ch)))
    cs

@[expose] noncomputable def natsSL (cs : List Char) : List Nat := natsRun cs (nat_lit 0) false

end CFSG.KS.DecSL

end
