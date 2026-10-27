module

public import CFSG.Sporadic.HeldB.CertPChainData
public import Certificates.Data.CFSGNative.Schreier.Check
import Certificates.Kernel.Sporadic.He.Order2112

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.HeldB CFSG.Monster.B.Co2.Native CFSG.Certificates.Native in
theorem certificate2112 : rawChainOK 8330 heGenArrs heStrongArrs heBase.toArray heWords 4 = true ∧
    rawOrbitSizes 8330 heStrongArrs heBase.toArray = [8330, 4480, 3, 18, 2] ∧
    isInvA 8330 heGenArrs[0]! (invCand 8330 heGenArrs[0]!) = true ∧
    isInvA 8330 heGenArrs[1]! (invCand 8330 heGenArrs[1]!) = true := KernelSpor.He2112.facts

end Certificates
