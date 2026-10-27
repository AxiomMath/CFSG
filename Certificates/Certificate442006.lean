module

public import Certificates.Data.OmegaS107Facts
import Certificates.Certificate2012
import Certificates.Data.PSp43Sylow
import Certificates.Kernel.A45Cls.Glue107

public section

namespace Certificates

open CertificateChecks

theorem certificate442006 : OmegaS107.Facts := KernelA45.facts442006

end Certificates
