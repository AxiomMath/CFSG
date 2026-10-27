module

public import Certificates.Data.Kernel.Spor.Prim
public import Certificates.Data.CFSGNative.SporadicSchreier.Count

public section

namespace CFSG.KC.O8

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def ordK (n w m idn R k : Nat) : Bool :=
  bAnd(Nat.beq (ppow n w m idn R k) idn,
    List.all (CFSG.Sporadic.Schreier.Native.divParts k) fun e =>
      bIf(Nat.beq (ppow n w m idn R e) idn, false, true))

end CFSG.KC.O8

end
