module

public import Certificates.Data.OmegaPkFacts
import Certificates.Certificate2012
import Certificates.Kernel.Pk442010.Facts

public section

namespace Certificates

open CertificateChecks

theorem certificate442010 : OmegaPk.Facts := KernelPk442010.facts

end Certificates
