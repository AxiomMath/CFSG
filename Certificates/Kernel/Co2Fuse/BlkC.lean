module

public import Certificates.Kernel.Co2Fuse.Data
import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSpor.Co2Fuse

open CFSG.KC.Co2Fuse CertificateChecks.KernelSpor.Co2Syl

theorem fusec : ∀ t < 256,
    fuseB E3.CF PT CI CA (RP 0) (RP 2) CNT 65536 (Nat.add 512 t) = true := by
  kc_cover 1

end CertificateChecks.KernelSpor.Co2Fuse

end
