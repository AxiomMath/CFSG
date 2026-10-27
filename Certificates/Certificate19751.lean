
module

public import CFSG.Open.LocalVocabulary
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.CoreD2K.M12.Glue

public section

namespace Certificates

theorem certificate19751 :
    ∃ (E : Subgroup ↥CFSG.Blueprint.NativeSporadic.M12)
      (Γ : Set ↥CFSG.Blueprint.NativeSporadic.M12),
      IsPGroup 3 E ∧ Subgroup.closure Γ = ⊤ ∧ ∀ g ∈ Γ,
        ∃ Y : Subgroup ↥CFSG.Blueprint.NativeSporadic.M12, Y ≤ E ∧ 2 ≤ CFSG.Open.pRank 3 Y ∧
          g ∈ Subgroup.normalizer (Y : Set ↥CFSG.Blueprint.NativeSporadic.M12) :=
  CertificateChecks.KernelCoreD2K.M12.coreGenerationOf_M12_three

end Certificates
