module

public import Certificates.Data.Kernel.O8.Core

public section

namespace CFSG.KC.O8

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.F4M

@[expose] noncomputable def mv4K (A v : Nat) : Nat :=
  orN (nat_lit 6) fun i => Nat.shiftLeft
    (Nat.land (sumN (nat_lit 6) fun k => Nat.mul (ent4 A i k) (fget v k (nat_lit 2))) (nat_lit 3))
    (Nat.mul (nat_lit 2) i)

@[expose] noncomputable def lettersOK (w : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun s _ ih => andB (Nat.blt s (nat_lit 6)) ih) w

@[expose] noncomputable def wMask (SW : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x _ ih => Nat.lor (pw2 (Nat.land x (nat_lit 4095))) ih) SW

end CFSG.KC.O8

end
