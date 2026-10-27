module

public import Certificates.Data.E27.Co1S0
import Certificates.Kernel.Co1B.C131301

public section

namespace Certificates

open CertificateChecks

theorem certificate131301 : CFSG.Sporadic.Co1.S0.co1S0Check () = true := KernelCo1B.S0131301.c131301

end Certificates
