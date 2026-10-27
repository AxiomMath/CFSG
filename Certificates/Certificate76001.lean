module

public import Certificates.Data.K76J2MaxCheck
import Certificates.Kernel.J2Max76

public section

namespace Certificates

open CertificateChecks

theorem certificate76001 : K76J2Max.check () = true := J2Max76.check_true

end Certificates
