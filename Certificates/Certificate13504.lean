module

public import Certificates.Certificate13504Base

public import CFSG.Sporadic.Schreier.Co1ThreeLocal
public import Certificates.Data.CFSGNative.Solomon.Co1T13
import Certificates.Kernel.Co1T13K.Glue
import Certificates.Certificate2043
import Certificates.Certificate3024

public section

open CFSG.Sporadic.Co1Schreier

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Co1Schreier in
theorem certificate13504 : y13Co1 ^ 13 = 1 ∧ y13Co1 ≠ 1 ∧
    ∀ c ∈ GA, c * y13Co1 = y13Co1 * c → c ^ 5 = 1 → c = 1 := KernelCo1T13K.c13504

end Certificates
