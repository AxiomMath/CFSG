module

public import Certificates.Kernel.Co2JRank.Data
public import Certificates.Kernel.Co2Syl.Small
public import CFSG.RankThree.Co2.WWordsData
import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSpor.Co2JRank

open CFSG.RankThree.Co2

theorem wGens : ∀ k < 5, Nat.beq (WG k) (CertificateChecks.KernelSpor.Co2Syl.wordK wGenWords[k]!) =
    true := by kc_cover 5

end CertificateChecks.KernelSpor.Co2JRank

end
