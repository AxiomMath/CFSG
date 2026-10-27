module

public import CFSG.Open.LocalVocabulary
public import CFSG.Sporadic.Schreier.RuDefs
import Certificates.Kernel.CoreD2K.RuPair.Glue

public section

namespace Certificates

theorem certificate19754 :
    ∃ (E : Subgroup ↥CFSG.Sporadic.RuSchreier.ruP) (Γ : Set ↥CFSG.Sporadic.RuSchreier.ruP),
      IsPGroup 5 E ∧ Subgroup.closure Γ = ⊤ ∧ ∀ g ∈ Γ,
        ∃ Y : Subgroup ↥CFSG.Sporadic.RuSchreier.ruP, Y ≤ E ∧ 2 ≤ CFSG.Open.pRank 5 Y ∧
          g ∈ Subgroup.normalizer (Y : Set ↥CFSG.Sporadic.RuSchreier.ruP) :=
  CertificateChecks.KernelCoreD2K.RuPair.coreGenerationOf_ruP_five

end Certificates
