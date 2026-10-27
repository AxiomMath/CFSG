module

public import Certificates.Data.Kernel.Misc.Coset.Act
public import Certificates.Data.Kernel.YModel.Model

public section

namespace CFSG.KC.MiscCoset.Act

@[expose] noncomputable def lineL (A : Nat → Nat) (L c : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => CFSG.KC.Loop.strictN acc (fun a =>
      Nat.lor a (Nat.shiftLeft (A (Nat.add (Nat.mul i L) c)) (Nat.mul (nat_lit 32) i))))

@[expose] noncomputable def invC (c : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Nat.succ c) (Nat.sub c (nat_lit 1))
    (Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 1))

@[expose] noncomputable def invRels (rels : List (List Nat)) : List (List Nat) :=
  List.rec (motive := fun _ => List (List Nat)) List.nil
    (fun r _ ih => List.cons
      (List.rec (motive := fun _ => List Nat) List.nil (fun c _ ih' => List.cons (invC c) ih') r) ih)
    rels

end CFSG.KC.MiscCoset.Act

end
