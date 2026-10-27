module

public import Certificates.Kernel.Co2Syl.D3
import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSpor.Co2Syl

open CFSG.KC.Co2Syl

theorem blk3b : ∀ t < 256, blkT E3.CF G3 (RP 3) (RP 0) CNT3 65536 (Nat.add 256 t) = true := by
  kc_cover 1

end CertificateChecks.KernelSpor.Co2Syl

end
