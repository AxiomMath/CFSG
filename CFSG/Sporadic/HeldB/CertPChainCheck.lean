module

public import CFSG.Sporadic.HeldB.CertPChainData
public import Certificates.Data.CFSGNative.Schreier.Check
public meta import CFSG.Sporadic.HeldB.CertPChainData
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import Certificates.Certificate2112

public section

namespace CFSG.Sporadic.HeldB

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem heChain_check :
    rawChainOK 8330 heGenArrs heStrongArrs heBase.toArray heWords 4 = true ∧
    rawOrbitSizes 8330 heStrongArrs heBase.toArray = [8330, 4480, 3, 18, 2] ∧
    isInvA 8330 heGenArrs[0]! (invCand 8330 heGenArrs[0]!) = true ∧
    isInvA 8330 heGenArrs[1]! (invCand 8330 heGenArrs[1]!) = true :=
  Certificates.certificate2112

end CFSG.Sporadic.HeldB
