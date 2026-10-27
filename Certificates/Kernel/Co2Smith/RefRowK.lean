module

public import Certificates.Kernel.Co2Smith.RefData
public import Certificates.Data.Kernel.Fi22Nbr3153
import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.N3153

theorem rows_ok : ∀ x < 2300, rowOK 2300 891 RR RM RS x = true := by
  kc_cover 64

theorem sym0_ok : ∀ i < 891, sym0OK RR RM i = true := by
  kc_cover 891

end CertificateChecks.KernelCo2Smith

end
