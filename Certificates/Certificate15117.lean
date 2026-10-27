module

public import Certificates.Data.GMS78RuSPrimeCheck
import Certificates.Kernel.GMS78.P117
import Certificates.Kernel.GMS78.PJ
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace Certificates

open CertificateChecks

theorem certificate15117 : CFSG.GMS78RuSP.checkA = true ∧ CFSG.GMS78RuSP.checkCa = true ∧
    CFSG.GMS78RuSP.checkCx = true ∧ CFSG.GMS78RuSP.checkF1 = true ∧
    CFSG.GMS78RuSP.checkF3 = true ∧ CFSG.GMS78RuSP.checkJd = true :=
  KernelGMS78.SD.checks15117

end Certificates
