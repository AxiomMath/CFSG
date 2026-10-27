module

public import Certificates.Kernel.Co2Syl.D1
import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSpor.Co2Syl

open CFSG.KC.Co2Syl

theorem blk1c : ∀ t < 256, blkT E1.CF G1 (RP 1) (RP 0) CNT1 131072 (Nat.add 512 t) = true := by
  kc_cover 1

end CertificateChecks.KernelSpor.Co2Syl

end
