module

public import Certificates.Data.Kernel.LocalQT.Sec

public section

namespace CFSG.KC.LayWords

open CFSG.KC.LQT

@[expose] noncomputable def codesInv (c : Lay) (X : Nat → Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) c.ONE
    (fun a _ acc => CFSG.KC.Loop.strictN acc fun y => c.mul (X (Nat.shiftRight a (nat_lit 1))) y) w

@[expose] noncomputable def codesOneInv (c : Lay) (X : Nat → Nat) (w : List Nat) : Bool :=
  Nat.beq (codesInv c X w) c.ONE

end CFSG.KC.LayWords

end
