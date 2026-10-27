module

public import CFSG.Sporadic.Co2Jc.Native.Simple
import Certificates.Kernel.Co2Jc.Simple

public section

namespace Certificates

open CertificateChecks

theorem certificate719020 :
    CFSG.Sporadic.Co2Jc.Native.simpleOK = true := KernelCo2Jc.simple_check

end Certificates
