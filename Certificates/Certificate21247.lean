module

public import CFSG.Sporadic.Co2Smith.GlNJInputs
import Certificates.Kernel.Co2Smith.NJ4

public section

namespace Certificates

open CertificateChecks

theorem certificate21247 :
    CFSG.Sporadic.Co2Smith.Native.glNJ4OK = true := KernelCo2Smith.nj4_ok

end Certificates
