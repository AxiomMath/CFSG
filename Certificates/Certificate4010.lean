module

public import CFSG.Sporadic.J4.QT2LocCntNative
import Certificates.Kernel.J4Q.C4010

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT2 in
theorem certificate4010 : (∀ c < 2048, c = 0 ∨ c ∈ tMasks ∨ c ∈ zMasks) := KernelJ4Q.c4010

end Certificates
