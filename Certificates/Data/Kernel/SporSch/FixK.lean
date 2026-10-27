module

public import Certificates.Data.Kernel.Spor.Raw

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def fixK (n w T : Nat) (L : List Nat) : Bool :=
  ((List.range n).filter fun p => Nat.beq (pg w (mask w) T p) p) == L

end CFSG.KS.SporSch

end
