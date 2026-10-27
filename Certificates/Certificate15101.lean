module

public import Certificates.Data.GMS78RuQCheck
import Certificates.Kernel.GMS78.Q

public section

namespace Certificates

open CertificateChecks

theorem certificate15101 : CFSG.GMS78RuQ.q0Check = true := KernelGMS78.q0Check_eq

end Certificates
