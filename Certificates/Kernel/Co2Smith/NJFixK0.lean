module

public import Certificates.Kernel.Co2Smith.NJFixDefs
import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

theorem njFix_k0_parts : ∀ c < 8, njFixK (0 + c * 32) 32 = true := by kc_cover 1

theorem njFix_k0 : njFixK 0 256 = true := njFixK_of_chunks 0 8 32 256 rfl njFix_k0_parts

end CertificateChecks.KernelCo2Smith
