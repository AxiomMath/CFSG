module

public import Certificates.Kernel.Co2J.Data
import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSpor.Co2J

open CFSG.KC.Co2J

theorem setsB : ∀ t < 358, setK PE SM EL INV CM RC EX MR 716 71 (Nat.add 358 t) = true := by
  kc_cover 16

end CertificateChecks.KernelSpor.Co2J

end
