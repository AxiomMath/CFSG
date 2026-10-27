module

import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KC.J4Q

@[expose] noncomputable def fldP (p j : Nat) : Nat := Nat.land (Nat.shiftRight p (Nat.mul 11 j)) 2047

@[expose] def unpackP (p : Nat) : List Nat := (List.range 11).map fun j => (p >>> (11 * j)) &&& 2047

@[expose] noncomputable def ONES : Nat := 1298708349570020393652962442872833

@[expose] noncomputable def actB (p c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun k acc => Nat.xor acc (Nat.mul (Nat.land (Nat.shiftRight c k) 1) (fldP p k))) 11

@[expose] noncomputable def compB (p q : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun k acc => Nat.xor acc (Nat.land (Nat.mul (Nat.land (Nat.shiftRight q k) ONES) 2047)
      (Nat.mul (fldP p k) ONES))) 11

end CFSG.KC.J4Q

end
