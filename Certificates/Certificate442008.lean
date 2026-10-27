module

public import Certificates.Data.OmegaAutQ
import Certificates.Kernel.OmegaAutQ.Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate442008 : OmegaAutQ.check () = true := KernelOmegaAutQ.check442008

end Certificates
