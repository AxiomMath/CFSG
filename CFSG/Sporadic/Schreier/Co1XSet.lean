module

public import CFSG.Sporadic.HS.CertSpec
public import CFSG.Sporadic.Schreier.Co1Base
public import Certificates.Data.CFSGNative.Co1.Data

public section

namespace CFSG.Sporadic.Co1Schreier

@[expose] def co1X : Set Vec24 :=
  {w | ∃ i < 98280, w = CFSG.Sporadic.SmallF2.toVecD 24
    ((CFSG.Sporadic.SmallF2.O CFSG.Sporadic.Co1.Native.co1Data).pts[i]!)}

end CFSG.Sporadic.Co1Schreier
