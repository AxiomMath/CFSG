module

public import Certificates.Data.Kernel.Misc.T84K

public section

namespace CFSG.KC.Misc.T84Q

open CFSG.KC.Misc.GL4

@[expose] noncomputable def andQ (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) false b a

@[expose] noncomputable def notQ (a : Bool) : Bool := Bool.rec (motive := fun _ => Bool) true false a

@[expose] noncomputable def allNQ (m : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i acc => andQ (f i) acc) m

@[expose] noncomputable def allLQ (L : List Nat) (f : Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ acc => andQ (f x) acc) L

@[expose] noncomputable def anyLQ (L : List Nat) (f : Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun x _ acc => Bool.rec (motive := fun _ => Bool) acc true (f x)) L

@[expose] noncomputable def q442350B (L : List Nat) : Bool :=
  allLQ L fun c => Nat.blt c (nat_lit 65536)

@[expose] noncomputable def q442350T (L : List Nat) : Bool :=
  allNQ (nat_lit 15) fun u =>
    anyLQ L fun c => Nat.beq (mul4F c (colC (nat_lit 1))) (colC (Nat.succ u))

@[expose] noncomputable def q442350F (L : List Nat) : Bool :=
  allNQ (nat_lit 14) fun u =>
    anyLQ L fun c => andQ (Nat.beq (mul4F c (colC (nat_lit 1))) (colC (nat_lit 1)))
      (notQ (Nat.beq (mul4F c (colC (Nat.succ (Nat.succ u)))) (colC (Nat.succ (Nat.succ u)))))

end CFSG.KC.Misc.T84Q
