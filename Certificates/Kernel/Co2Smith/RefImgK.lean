module

public import Certificates.Kernel.Co2Smith.RefData
public import Certificates.Kernel.Sporadic.Co2.ChainA
public import Certificates.Data.Kernel.Fi22Nbr3153
import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.N3153 CertificateChecks.KernelSpor

theorem img0_ok : ∀ x < 2300, imgOK 2300 891 (Co2A.S 0) RR RM x = true := by
  kc_cover 64

theorem img1_ok : ∀ x < 2300, imgOK 2300 891 (Co2A.S 1) RR RM x = true := by
  kc_cover 64

theorem tree_ok : ∀ x < 2300, treeOK 2300 2 Co2A.S RT x = true := by
  kc_cover 1150

end CertificateChecks.KernelCo2Smith

end
