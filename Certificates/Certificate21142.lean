module

public import CFSG.Sporadic.Co1Patterson.TwistNativeInputs
import Certificates.Kernel.Co1B.C21142

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Co1Patterson.TwistNative in
theorem certificate21142 : countOK = true := KernelCo1B.c21142

end Certificates
