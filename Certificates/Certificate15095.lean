module

public import Certificates.Data.GMS78RuSModelCheck
import Certificates.Kernel.GMS78.S95
import Certificates.Kernel.GMS78.S16K
import Certificates.Kernel.GMS78.S17Inv
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.GMS78.S95Data
import Certificates.Kernel.GMS78.P117Data
import Certificates.Data.Kernel.GMS78RuSGrp

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelGMS78.SD in
theorem certificate15095 : CFSG.GMS78RuS.check16 false = true ∧ CFSG.GMS78RuS.check16 true = true ∧
    CFSG.GMS78RuS.check17 false = true ∧ CFSG.GMS78RuS.check17 true = true :=
  ⟨check16_false, check16_true, check17_false, check17_true⟩

end Certificates
