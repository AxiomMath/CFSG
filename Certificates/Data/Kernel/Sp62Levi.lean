module

public import Certificates.Data.Kernel.Sp62Twin

public section

namespace CFSG.KD.Sp62

open CFSG.KC.Loop

@[expose] noncomputable def any3 (f : Nat → Bool) : Bool := f 0 || (f 1 || f 2)

@[expose] noncomputable def leviZ (Z0 Z1 Z2 Z Y : Nat) : Bool :=
  any3 fun a => any3 fun b => Nat.beq (MULF Y Z) (MULF (VC Z0 Z1 Z2 a b 0) Y)

@[expose] noncomputable def leviF (Z0 Z1 Z2 Y : Nat) : Bool :=
  leviZ Z0 Z1 Z2 Z0 Y && leviZ Z0 Z1 Z2 Z1 Y

@[expose] noncomputable def leviK (R : Nat → Nat) (Z0 Z1 Z2 o n hi : Nat) : Bool :=
  allBelow n hi fun t => leviF Z0 Z1 Z2 (recX R o t)

end CFSG.KD.Sp62

end
