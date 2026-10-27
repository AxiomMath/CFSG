module

public import CFSG.Sporadic.Co2Jc.Native.Derived
import Certificates.Kernel.Co2Jc.Derived

public section

namespace Certificates

open CertificateChecks

theorem certificate719010 :
    CFSG.Sporadic.Co2Jc.Native.derivedOK = true := KernelCo2Jc.derived_check

end Certificates
