module

public import CFSG.Sporadic.Co2Smith.GlU62SteinInputs
import Certificates.Kernel.Co2Smith.Stein

public section

namespace Certificates

open CertificateChecks

theorem certificate21185 :
    CFSG.Sporadic.Co2Smith.Native.glSteinOK = true := KernelCo2Smith.stein_ok

end Certificates
