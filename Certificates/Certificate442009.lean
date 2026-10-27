module

public import Certificates.Data.OmegaSplitFacts
import Certificates.Certificate2012
import Certificates.Certificate23100
import Certificates.Certificate442002
import Certificates.Kernel.A45Cls.GlueSplit

public section

namespace Certificates

open CertificateChecks

theorem certificate442009 : OmegaSplit.Facts := KernelA45.factsSplit

end Certificates
