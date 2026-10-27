module

public import Certificates.Data.Kernel.LocalQT.Lat

public section

namespace CFSG.KC.LQT.NP

open CFSG.KC.Ord CFSG.KC.LQT.L

@[expose] noncomputable def revN (l : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun x _ ih acc => ih (List.cons x acc)) l []

@[expose] noncomputable def letO (y : Nat) (k : Nat → Option (List Nat)) : Option (List Nat) :=
  Nat.rec (motive := fun _ => Option (List Nat)) (k (nat_lit 0)) (fun m _ => k (Nat.succ m)) y

@[expose] noncomputable def natsK (cs : List Char) : Option (List Nat) :=
  List.rec (motive := fun _ => List Nat → Nat → Bool → Option (List Nat))
    (fun acc cur t => some (revN (Bool.rec (motive := fun _ => List Nat) acc (List.cons cur acc) t)))
    (fun c _ ih acc cur t => letO (Char.toNat c) fun k =>
      Bool.rec (motive := fun _ => Option (List Nat))
        (Bool.rec (motive := fun _ => Option (List Nat)) none
          (letO (Nat.add (Nat.mul cur 10) (Nat.sub k 48)) fun v => ih acc v true)
          (andB (Nat.ble 48 k) (Nat.ble k 57)))
        (ih (Bool.rec (motive := fun _ => List Nat) acc (List.cons cur acc) t) 0 false)
        (Nat.beq k 32))
    cs [] 0 false

@[expose] noncomputable def natsOK (cs : List Char) (L : List Nat) : Bool :=
  Option.rec (motive := fun _ => Bool) false (fun l => eqL l L) (natsK cs)

end CFSG.KC.LQT.NP

end
