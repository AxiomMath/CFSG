module

public import Certificates.Kernel.Co1B.Vecs
public import Certificates.Kernel.Co1Cover.EData
public import Certificates.Data.Kernel.Co1BFix
public import Certificates.Data.Kernel.Co1F2
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.C24531

open CFSG.KC.Co1F2 CFSG.KC.Co1B CertificateChecks.KernelCo1Cover.ECore

theorem xA : Nat.beq (fixTabK (trK 24 EAP) CV.F 117) 2280 = true := by quickRfl
theorem xC : Nat.beq (fixTabK (trK 24 ECP) CV.F 117) 264 = true := by quickRfl

end CertificateChecks.KernelCo1B.C24531

end
