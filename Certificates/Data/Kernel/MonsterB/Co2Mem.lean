module

public import CFSG.Certificates.Kernel.Enum.Defs
public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KC.Co2Mem

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def memK (n w F y : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) false
    (fun t r => Bool.rec r true (Nat.beq (pg w (mask w) F t) y)) n

end CFSG.KC.Co2Mem

end
