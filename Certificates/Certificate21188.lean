module

public import CFSG.Sporadic.Co2Smith.GlU62Inputs
import Certificates.Kernel.Co2Smith.U62

public section

namespace Certificates

open CertificateChecks

theorem certificate21188 :
    CFSG.Sporadic.Co2Smith.Native.u62OK = true := KernelCo2Smith.u62_ok

end Certificates
