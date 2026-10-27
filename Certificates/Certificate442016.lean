module

public import Certificates.Data.OmegaOuter
import Certificates.Certificate2012
import Certificates.Kernel.A45Cls.Glue442016

public section

namespace Certificates

open CertificateChecks

theorem certificate442016 : OmegaOuter.check () = true := KernelA45.check442016

end Certificates
