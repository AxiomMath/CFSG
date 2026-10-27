module

public import CFSG.Open.LocalVocabulary
public import CFSG.Sporadic.Schreier.TitsCert
import Certificates.Kernel.CoreD2K.Tits.Glue

public section

namespace Certificates

theorem certificate19750 :
    ∃ (E : Subgroup ↥CFSG.Sporadic.Schreier.Tits.titsD)
      (Γ : Set ↥CFSG.Sporadic.Schreier.Tits.titsD),
      IsPGroup 3 E ∧ Subgroup.closure Γ = ⊤ ∧ ∀ g ∈ Γ,
        ∃ Y : Subgroup ↥CFSG.Sporadic.Schreier.Tits.titsD, Y ≤ E ∧ 2 ≤ CFSG.Open.pRank 3 Y ∧
          g ∈ Subgroup.normalizer (Y : Set ↥CFSG.Sporadic.Schreier.Tits.titsD) :=
  CertificateChecks.KernelCoreD2K.Tits.coreGenerationOf_titsD_three

end Certificates
