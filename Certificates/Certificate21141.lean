module

public import CFSG.Sporadic.Co1Patterson.TwistNativeInputs
import Certificates.Kernel.Co1B.C21141

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Co1Patterson.TwistNative in
theorem certificate21141 : (dagOK = true)
    ∧ (yFormOK = true)
    ∧ (elemsOK = true)
    ∧ (irrOK = true)
    ∧ (uOK = true)
    ∧ (uSetOK = true)
    ∧ (h4OK = true)
    ∧ (nwcOK = true)
    ∧ (signOK = true) := KernelCo1B.c21141

end Certificates
