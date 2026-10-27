module

public import CFSG.Sporadic.Co2Smith.GlDataInputs
import Certificates.Kernel.Co2Smith.ChainN

public section

namespace Certificates

open CertificateChecks

theorem certificate21124 :
    CFSG.Sporadic.Co2Smith.Native.glChainNOK = true := KernelCo2Smith.chainN_ok

end Certificates
