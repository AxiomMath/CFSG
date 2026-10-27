module

public import CFSG.Sporadic.SuzOddCore.InvArraysCheck
public import Certificates.Data.CFSGNative.Schreier.Check
public meta import CFSG.Sporadic.SuzOddCore.InvArraysCheck
public meta import Certificates.Data.CFSGNative.Schreier.Check
import Certificates.Kernel.Sporadic.SuzInv.Final3

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2.Native CFSG.Certificates.Native in
theorem certificate2300 : rawChainOK 1782 (invFullGenArrs 3) (invFullStrongArrs 3) (invFullBases.getD 3 []).toArray
      (invFullDerivs 3) 4 = true ∧
    (rawOrbitSizes 1782 (invFullStrongArrs 3) (invFullBases.getD 3 []).toArray).prod = 2419200 ∧
    rawChainOK 1782 (invInnerGenArrs 3) (invInnerStrongArrs 3)
      (invInnerBases.getD 3 []).toArray (invInnerDerivs 3) 4 = true ∧
    (rawOrbitSizes 1782 (invInnerStrongArrs 3) (invInnerBases.getD 3 []).toArray).prod =
      1209600 := KernelSpor.SuzInv.facts3

end Certificates
