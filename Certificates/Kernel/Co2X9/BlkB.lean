module

public import Certificates.Kernel.Co2X9.Data
import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSpor.Co2X9

open CFSG.KC.Co2X9

theorem blkB : ∀ t < 48, blkX EN.CF GX DX WK 6144 (Nat.add 48 t) = true := by
  kc_cover 1

end CertificateChecks.KernelSpor.Co2X9

end
