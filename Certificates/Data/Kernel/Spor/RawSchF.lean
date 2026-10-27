module

public import Certificates.Data.Kernel.Spor.Raw

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def fwdT (T : Nat) : Nat :=
  Nat.sub T (Nat.sub (stCnt T) (Nat.shiftRight (stCnt T) (nat_lit 1)))

end CFSG.KS.Raw

end
