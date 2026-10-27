module

public import Certificates.Data.OmegaSwap
import Certificates.Certificate2012
import Certificates.Kernel.A45Cls.Glue442017

public section

namespace Certificates

open CertificateChecks

theorem certificate442017 : OmegaSwap.check () = true := KernelA45.check442017

end Certificates
