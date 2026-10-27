module

public import Certificates.Kernel.Co2Syl.D6
import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSpor.Co2Syl

open CFSG.KC.Co2Syl

theorem blk6 : ∀ t < 256, blkT E6.CF G6 (RP 6) (RP 0) CNT6 16384 t = true := by
  kc_cover 1

end CertificateChecks.KernelSpor.Co2Syl

end
