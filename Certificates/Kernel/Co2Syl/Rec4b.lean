module

public import Certificates.Kernel.Co2Syl.D4
import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSpor.Co2Syl

open CFSG.KC.Co2Syl

theorem blk4b : ∀ t < 256, blkT E4.CF G4 (RP 4) (RP 0) CNT4 32768 (Nat.add 256 t) = true := by
  kc_cover 1

end CertificateChecks.KernelSpor.Co2Syl

end
