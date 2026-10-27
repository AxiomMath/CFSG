module

public import CFSG.Sporadic.Schreier.Co1StabCheck
public import CFSG.Sporadic.Schreier.Co1QuotData
public import CFSG.Sporadic.Co2Cert.Data
public meta import CFSG.Sporadic.Schreier.Co1StabCheck
public meta import CFSG.Sporadic.Schreier.Co1QuotData
public meta import CFSG.Sporadic.Schreier.Co1StabData
public meta import CFSG.Sporadic.Schreier.Co1OrbEnumCheck
public meta import CFSG.Sporadic.Schreier.Co1FullOrbCheck
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import CFSG.Sporadic.Co2Cert.Data
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public meta import Certificates.Data.CFSGNative.Th.Tables
public meta import Certificates.Data.CFSGNative.Th.Orbit

public section

namespace CFSG.Sporadic.Co1Schreier

namespace Native

@[expose] def quotCheckOf (a0 a1 : Array Nat) : Bool :=
  Data.quotAct0.toArray == a0 && Data.quotAct1.toArray == a1 &&
    hRows0 == Data.subRows0.toArray && hRows1 == Data.subRows1.toArray

@[expose] def quotCheck : Bool :=
  quotCheckOf CFSG.Sporadic.Co2Cert.co2OrigArrs[0]! CFSG.Sporadic.Co2Cert.co2OrigArrs[1]!

end Native

end CFSG.Sporadic.Co1Schreier
