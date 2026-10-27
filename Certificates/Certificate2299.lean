module

public import CFSG.Sporadic.SuzOddCore.InvArraysCheck
public import Certificates.Data.CFSGNative.Schreier.Check
public meta import CFSG.Sporadic.SuzOddCore.InvArraysCheck
public meta import Certificates.Data.CFSGNative.Schreier.Check
import Certificates.Kernel.Sporadic.SuzInv.Final2

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2.Native CFSG.Certificates.Native in
theorem certificate2299 : rawChainOK 1782 (invFullGenArrs 2) (invFullStrongArrs 2) (invFullBases.getD 2 []).toArray
      (invFullDerivs 2) 4 = true ∧
    (rawOrbitSizes 1782 (invFullStrongArrs 2) (invFullBases.getD 2 []).toArray).prod = 380160 ∧
    rawChainOK 1782 (invInnerGenArrs 2) (invInnerStrongArrs 2)
      (invInnerBases.getD 2 []).toArray (invInnerDerivs 2) 4 = true ∧
    (rawOrbitSizes 1782 (invInnerStrongArrs 2) (invInnerBases.getD 2 []).toArray).prod =
      190080 := KernelSpor.SuzInv.facts2

end Certificates
