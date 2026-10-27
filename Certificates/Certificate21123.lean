module

public import CFSG.Sporadic.Co2Smith.GlDataInputs
import Certificates.Kernel.Co2Smith.Wit

public section

namespace Certificates

open CertificateChecks

theorem certificate21123 :
    CFSG.Sporadic.Co2Smith.Native.glWitOK = true := KernelCo2Smith.wit_ok

end Certificates
