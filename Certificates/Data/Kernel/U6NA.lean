module

public import Certificates.Data.Kernel.F4NA
public import Certificates.Data.Kernel.U6Three.Defs

public section

namespace CFSG.KC.U6NA

open CFSG.KC.U6Three CFSG.KC.F4NA CFSG.KC.Loop

@[expose] def pn (a : Nat) : Nat := Nat.succ a

@[expose] def tm (t a : Nat) : Nat := Bool.rec (motive := fun _ => Nat) 0 (pn a) (Nat.beq t 0)

@[expose] def trN (c : Nat) : Bool :=
  Nat.beq (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (tm (dig c 6) (dig c 0))
    (tm (dig c 6) (dig c 1))) (tm (dig c 6) (dig c 2))) (tm (dig c 7) (dig c 3)))
    (tm (dig c 7) (dig c 4))) (tm (dig c 7) (dig c 5))) 0

@[expose] def blkN (c : Nat) : Bool := Nat.beq (Nat.mod (dig c 0 + dig c 1 + dig c 2) 3) 0

@[expose] def torN (c : Nat) : Bool := Nat.beq (dig c 6) 0 && Nat.beq (dig c 7) 0

@[expose] noncomputable def cov6B (TP M : Nat) : Bool :=
  allBelow 729 12 fun i => Bool.rec (motive := fun _ => Bool) (bt M i) true (torN (tabN TP i))

end CFSG.KC.U6NA

end
