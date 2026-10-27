module

public import Certificates.Data.Kernel.WittCnt

public section

namespace CFSG.KC.WCnt

@[expose] noncomputable def badT (E V₀ V₁ : Nat) (Vs : List Nat) (y : Nat) : Bool :=
  bAnd(relT E E y, bIf(bAnd(relAny V₀ Vs y, relAny V₁ Vs y), false, true))

end CFSG.KC.WCnt

end
