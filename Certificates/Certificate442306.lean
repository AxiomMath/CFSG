module

public import Certificates.Data.OmegaT11
import Certificates.Certificate2012
import Certificates.Kernel.A45Cls.CheckT11

public section

namespace Certificates

open CertificateChecks

theorem certificate442306 : OmegaT11.check () = true := KernelA45.omegaT11_check

end Certificates
