module

public import CFSG.Sporadic.Co2Smith.GlNJInputs
import Certificates.Kernel.Co2Smith.NJ2

public section

namespace Certificates

open CertificateChecks

theorem certificate21169 :
    CFSG.Sporadic.Co2Smith.Native.glNJ2OK = true := KernelCo2Smith.nj2_ok

end Certificates
