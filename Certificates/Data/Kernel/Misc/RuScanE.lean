module

public import Certificates.Data.Kernel.Misc.RuScanB

public section

namespace CFSG.KC.Misc.RuScan

open CFSG.KC.Enum

@[expose] noncomputable def lbK (V : Nat → Nat) (n : Nat) : Bool :=
  allN 256 (fun l => Nat.blt l n || Nat.beq (V (64 + 32 * l + 28)) 0 ||
    Nat.blt 7 (V (64 + 32 * l + 28)))

end CFSG.KC.Misc.RuScan

end
