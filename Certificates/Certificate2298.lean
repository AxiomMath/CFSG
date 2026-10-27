module

public import CFSG.Sporadic.SuzOddCore.InvArraysCheck
public import Certificates.Data.CFSGNative.Schreier.Check
public meta import CFSG.Sporadic.SuzOddCore.InvArraysCheck
public meta import Certificates.Data.CFSGNative.Schreier.Check
import Certificates.Kernel.Sporadic.SuzInv.Final1

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2.Native CFSG.Certificates.Native in
theorem certificate2298 : rawChainOK 1782 (invFullGenArrs 1) (invFullStrongArrs 1) (invFullBases.getD 1 []).toArray
      (invFullDerivs 1) 4 = true ∧
    (rawOrbitSizes 1782 (invFullStrongArrs 1) (invFullBases.getD 1 []).toArray).prod = 6635520 ∧
    rawChainOK 1782 (invInnerGenArrs 1) (invInnerStrongArrs 1)
      (invInnerBases.getD 1 []).toArray (invInnerDerivs 1) 4 = true ∧
    (rawOrbitSizes 1782 (invInnerStrongArrs 1) (invInnerBases.getD 1 []).toArray).prod =
      3317760 := KernelSpor.SuzInv.facts1

end Certificates
