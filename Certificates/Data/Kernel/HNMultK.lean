module

public import CFSG.Certificates.Kernel.Orders.Cert
public import Certificates.Data.Kernel.Spor.WordProg

public section

namespace CFSG.KC.HNMult

open CFSG.KC.Ord

@[expose] noncomputable def decL (w : List Nat) : List (Nat × Bool) :=
  List.rec (motive := fun _ => List (Nat × Bool)) List.nil (fun c _ ih => List.cons (letC c) ih) w

@[expose] noncomputable def relW (RB : Nat → Nat) (mul : Nat → Nat → Nat) (L ONE : Nat)
    (w : List Nat) : Bool :=
  andB (relsBounded (List.cons (decL w) List.nil) L)
    (relOK RB mul (List.cons (decL w) List.nil) L ONE (nat_lit 0))

@[expose] noncomputable def relWRange (RB : Nat → Nat) (mul : Nat → Nat → Nat) (L ONE : Nat)
    (RW : Nat → List Nat) (lo n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun k ih => andB ih (relW RB mul L ONE (RW (Nat.add lo k)))) n
end CFSG.KC.HNMult

end
