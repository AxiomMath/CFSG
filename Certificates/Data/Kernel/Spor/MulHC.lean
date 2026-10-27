module

public import Certificates.Data.Kernel.Spor.MulH

public section

namespace CFSG.KS.MulH

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PEnum

@[expose] noncomputable def clRK (k K cnt : Nat) (T POS Q CL : Nat → Nat) (c : Nat) : Bool :=
  strictB (Nat.mod c K) (fun j => bIf(Nat.blt j k,
    Nat.beq (r32 CL c) (r32 POS (Nat.add (Nat.mul (Nat.div c K) k) j)),
    findPtK cnt T Q CL c))

end CFSG.KS.MulH

end
