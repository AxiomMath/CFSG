module

public import Certificates.Kernel.Co2Syl.D8
import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSpor.Co2Syl

open CFSG.KC.Co2Syl

theorem blk8 : ∀ t < 256, blkT E8.CF G8 (RP 8) (RP 0) CNT8 16384 t = true := by
  kc_cover 1

end CertificateChecks.KernelSpor.Co2Syl

end
