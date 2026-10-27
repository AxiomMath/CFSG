module

public import Certificates.Data.GMS78RuSimCheck
import Certificates.Kernel.GMS78.S

public section

namespace Certificates

open CertificateChecks

theorem certificate15092 : CFSG.GMS78RuSim.s0Check = true ∧ CFSG.GMS78RuSim.s1Check = true ∧
    CFSG.GMS78RuSim.s2aCheck = true ∧ CFSG.GMS78RuSim.s2bCheck = true := KernelGMS78.sChecks_eq

end Certificates
