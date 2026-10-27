module

public import CFSG.Sporadic.SuzOddCore.InvArraysCheck
public import Certificates.Data.CFSGNative.Schreier.Check
public meta import CFSG.Sporadic.SuzOddCore.InvArraysCheck
public meta import Certificates.Data.CFSGNative.Schreier.Check
import Certificates.Kernel.Sporadic.SuzInv.Final0

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2.Native CFSG.Certificates.Native in
theorem certificate2297 : rawChainOK 1782 (invFullGenArrs 0) (invFullStrongArrs 0) (invFullBases.getD 0 []).toArray
      (invFullDerivs 0) 4 = true ∧
    (rawOrbitSizes 1782 (invFullStrongArrs 0) (invFullBases.getD 0 []).toArray).prod = 322560 ∧
    rawChainOK 1782 (invInnerGenArrs 0) (invInnerStrongArrs 0)
      (invInnerBases.getD 0 []).toArray (invInnerDerivs 0) 4 = true ∧
    (rawOrbitSizes 1782 (invInnerStrongArrs 0) (invInnerBases.getD 0 []).toArray).prod =
      161280 := KernelSpor.SuzInv.facts0

end Certificates
