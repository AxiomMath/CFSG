module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalTab
import Certificates.Kernel.U42Syl.Checks
import CFSG.Certificates.Kernel.U42Syl.Sound
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalGroups

public section

open CFSG.AGLEmbedding.KFactProofs.Sp62Local CertificateChecks.KernelU42Syl

namespace Certificates

open CFSG.AGLEmbedding.KFactProofs.Sp62Local in
theorem certificate465001 : ∀ x ∈ Hgen gensV, x ≠ 1 → x ^ 5 = 1 → Hgen gensV ≤ Hgen gensT ⊔ Subgroup.zpowers x :=
  fun _ hx hx1 hx5 => CFSG.KC.U42Syl.order5_cover_of_checks ch465001_tab ch465001_rep
    (CFSG.KC.U42Syl.recB_append ch465001_rec3 _ _ (CFSG.KC.U42Syl.recB_append ch465001_rec2 _ _
      (CFSG.KC.U42Syl.recB_append ch465001_rec1 _ _ ch465001_rec0)))
    (by rw [List.length_append, List.length_append, List.length_append]; exact ch465001_len)
    card_V0 T0_le_V0 hx hx1 hx5

end Certificates
