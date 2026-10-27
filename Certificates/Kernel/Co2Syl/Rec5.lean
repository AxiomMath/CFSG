module

public import Certificates.Kernel.Co2Syl.D5
import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSpor.Co2Syl

open CFSG.KC.Co2Syl

theorem blk5 : ∀ t < 256, blkT E5.CF G5 (RP 5) (RP 0) CNT5 16384 t = true := by
  kc_cover 1

end CertificateChecks.KernelSpor.Co2Syl

end
