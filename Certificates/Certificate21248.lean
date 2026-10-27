module

public import CFSG.Sporadic.Co2Smith.GlNJInputs
import Certificates.Kernel.Co2Smith.NJFix

public section

namespace Certificates

open CertificateChecks

theorem certificate21248 :
    CFSG.Sporadic.Co2Smith.Native.glNJFixOK = true := KernelCo2Smith.njFix_ok

end Certificates
