module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalTab
import Certificates.Kernel.Sp62W.ChecksDC
import Certificates.Kernel.Sp62Syl.Checks
import CFSG.Certificates.Kernel.Sp62Syl.Sound
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalGroups

public section

open CFSG.AGLEmbedding.KFactProofs.Sp62Local CertificateChecks.KernelSp62Syl

namespace Certificates

open CertificateChecks

open CFSG.AGLEmbedding.KFactProofs.Sp62Local CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two in
theorem certificate465002 : ∀ g : H6, g ∉ Hgen gensWD → Hgen gensWD ≤ Hgen gensT ⊔ Subgroup.zpowers g :=
  fun _ hg => CFSG.KC.Sp62Syl.le_of_not_mem_W card_W0 KernelSp62W.ch9443dc ch465002_q
    ch465002_t ch465002_r ch465002_len ch465002_c ch465002_k0 hg

end Certificates
