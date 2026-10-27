module

public import Certificates.Data.Kernel.AS35QTS.Checks

public section

namespace CFSG.KC.AS35QTS

@[expose] noncomputable def lensOK (G S IL W V0 : List Nat) : Bool :=
  Bool.and' (Nat.beq (lenR G) 648) (Bool.and' (Nat.beq (lenR S) 36)
    (Bool.and' (Nat.beq (lenR IL) 127) (Bool.and' (Nat.beq (lenR W) 90) (Nat.beq (lenR V0) 10))))

end CFSG.KC.AS35QTS

end
