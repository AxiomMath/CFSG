module

public import CFSG.Sporadic.Co2Jc.Native.Orbits
import Certificates.Kernel.Co2Jc.Orbits

public section

namespace Certificates

open CertificateChecks

theorem certificate719001 :
    CFSG.Sporadic.Co2Jc.Native.orbitsOK = true := KernelCo2Jc.orbits_check

end Certificates
