module

public import CFSG.Sporadic.Co2Smith.GlDataInputs
import Certificates.Kernel.Co2Smith.Elem

public section

namespace Certificates

open CertificateChecks

theorem certificate21120 :
    CFSG.Sporadic.Co2Smith.Native.glElemOK = true := KernelCo2Smith.elem_ok

end Certificates
