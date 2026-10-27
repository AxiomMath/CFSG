module

public import Certificates.Data.E4O8TwoTwins
import Certificates.Kernel.OmegaEight.E4O8TwinsGlue

public section

namespace Certificates

open CertificateChecks

theorem certificate393005 : E4O8TwoTwins.check () = true := KernelO8.e4_two_twins

end Certificates
