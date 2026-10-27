module

public import Certificates.Data.GMS78RuNCoord
import Certificates.Kernel.GMS78.N

public section

namespace Certificates

open CertificateChecks

theorem certificate15118 : CFSG.GMS78RuN.gamColCheck = true ∧ CFSG.GMS78RuN.dPartCheck = true := KernelGMS78.nCoord_eq

end Certificates
