module

public import CFSG.Sporadic.Co2Smith.GlCosetInputs
import Certificates.Kernel.Co2Smith.Lab

public section

namespace Certificates

open CertificateChecks

theorem certificate21173 :
    CFSG.Sporadic.Co2Smith.Native.glCosetLabOK = true := KernelCo2Smith.cosetLab_ok

end Certificates
