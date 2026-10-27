module

public import CFSG.Sporadic.Co2Smith.GlCosetInputs
import Certificates.Kernel.Co2Smith.CosetElem

public section

namespace Certificates

open CertificateChecks

theorem certificate21170 :
    CFSG.Sporadic.Co2Smith.Native.glCosetElemOK = true := KernelCo2Smith.cosetElem_ok

end Certificates
