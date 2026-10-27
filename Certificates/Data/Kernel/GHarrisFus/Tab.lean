module

public import Certificates.Data.Kernel.GHarrisFus.Defs

public section

namespace CFSG.KC.GHFus

open CFSG.KC.Enum

@[expose] noncomputable def allBelow (n : Nat) (p : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => Bool.and' (p i) ih) n

@[expose] noncomputable def dmP : Nat :=
  nat_lit 7299427748293135508666912717695448455147873746853017753162171213942703272464

@[expose] noncomputable def meP : Nat := nat_lit 19842493303511274935107897925391693002375425

@[expose] noncomputable def meN (d i k : Nat) : Nat :=
  Nat.land (Nat.shiftRight meP (Nat.shiftLeft (Nat.add (Nat.add (Nat.mul (nat_lit 9) d)
    (Nat.mul (nat_lit 3) i)) k) (nat_lit 1))) (nat_lit 3)

@[expose] noncomputable def rowN (d i w : Nat) : Nat :=
  Nat.mod (Nat.add (Nat.add
    (Nat.mul (meN d i (nat_lit 0)) (Nat.land (Nat.shiftRight w (nat_lit 4)) (nat_lit 3)))
    (Nat.mul (meN d i (nat_lit 1)) (Nat.land (Nat.shiftRight w (nat_lit 2)) (nat_lit 3))))
    (Nat.mul (meN d i (nat_lit 2)) (Nat.land w (nat_lit 3)))) (nat_lit 4)

@[expose] noncomputable def mvN (d w : Nat) : Nat :=
  Nat.add (Nat.add (Nat.mul (nat_lit 16) (rowN d (nat_lit 0) w)) (Nat.mul (nat_lit 4) (rowN d (nat_lit 1) w)))
    (rowN d (nat_lit 2) w)

@[expose] noncomputable def dmOK (dm : Nat) : Bool :=
  allBelow (nat_lit 64) fun i =>
    Nat.beq (Nat.land (Nat.shiftRight dm (Nat.shiftLeft i (nat_lit 2))) (nat_lit 7))
      (Nat.land (Nat.shiftRight dmP (Nat.shiftLeft i (nat_lit 2))) (nat_lit 15))

@[expose] noncomputable def mvOK (mv : Nat) : Bool :=
  allBelow (nat_lit 512) fun i =>
    Nat.beq (Nat.land (Nat.shiftRight mv (Nat.shiftLeft i (nat_lit 3))) (nat_lit 63))
      (mvN (Nat.shiftRight i (nat_lit 6)) (Nat.land i (nat_lit 63)))

@[expose] noncomputable def ctFrom (CT : Nat) (l : List Nat) (j : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih j => Bool.and' (Nat.beq (clsK CT j) x) (strictB (Nat.succ j) ih)) l j

@[expose] noncomputable def ctOK (CT : Nat) (l : List Nat) : Bool := ctFrom CT l (nat_lit 0)

end CFSG.KC.GHFus
