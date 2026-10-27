module

public import Certificates.Data.Seitz77CaseB45Data
public meta import Certificates.Data.Seitz77CaseB45Data
import Certificates.Kernel.Seitz.B45G

public section

namespace Certificates

open CertificateChecks

theorem certificate6134 : Seitz77CaseB45.fbSixCheck = true := KernelSeitz.fbSix_true

end Certificates
