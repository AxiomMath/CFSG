module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutFusionInputs
public import Certificates.Certificate11003

public section

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.M12Cover CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier CFSG.ComponentClassification.OuterAutomorphisms

namespace CertificateChecks.Batch11002

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.M12Cover CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier CFSG.ComponentClassification.OuterAutomorphisms

private theorem permR_apply_0 : ∀ i, permR i = ![0, 1, 10, 5, 8, 3, 11, 7, 4, 9, 2, 6] i := by
  decide +kernel

private theorem permS_apply_1 : ∀ i, permS i = ![1, 0, 2, 3, 8, 5, 11, 9, 4, 7, 10, 6] i := by
  decide +kernel

private theorem permH_word_2 : permH = m12gA * m12gB * m12gB * m12gA * m12gB * m12gA * m12gB * m12gB *
    m12gA * m12gB * m12gA * m12gB * m12gA * m12gB * m12gA * m12gB := by
  decide +kernel

private theorem permH_word_list_3 : permH = ([1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2].map
    fun k : ℕ => if k = 1 then m12gA else m12gB).prod := by
  decide +kernel

private theorem permH_apply_4 : ∀ i, permH i = ![3, 6, 2, 5, 0, 7, 11, 4, 8, 10, 1, 9] i := by
  decide +kernel

private theorem permH_word_pow_5 : permH = m12gA * m12gB ^ 2 * m12gA * m12gB * m12gA * m12gB ^ 2 * m12gA *
    m12gB * m12gA * m12gB * m12gA * m12gB * m12gA * m12gB := by
  decide +kernel

private theorem permH_conj_6 : permH * permZ * permH⁻¹ = permZ * permR := by
  decide +kernel

end CertificateChecks.Batch11002

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.M12Cover CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier CFSG.ComponentClassification.OuterAutomorphisms in
theorem certificate11002 : (
∀ i, permR i = ![0, 1, 10, 5, 8, 3, 11, 7, 4, 9, 2, 6] i
)
    ∧ (
∀ i, permS i = ![1, 0, 2, 3, 8, 5, 11, 9, 4, 7, 10, 6] i
)
    ∧ (
permH = m12gA * m12gB * m12gB * m12gA * m12gB * m12gA * m12gB * m12gB *
    m12gA * m12gB * m12gA * m12gB * m12gA * m12gB * m12gA * m12gB
)
    ∧ (
permH = ([1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2].map
    fun k : ℕ => if k = 1 then m12gA else m12gB).prod
)
    ∧ (
∀ i, permH i = ![3, 6, 2, 5, 0, 7, 11, 4, 8, 10, 1, 9] i
)
    ∧ (
permH = m12gA * m12gB ^ 2 * m12gA * m12gB * m12gA * m12gB ^ 2 * m12gA *
    m12gB * m12gA * m12gB * m12gA * m12gB * m12gA * m12gB
)
    ∧ (
permH * permZ * permH⁻¹ = permZ * permR
) := by
  exact ⟨CertificateChecks.Batch11002.permR_apply_0, CertificateChecks.Batch11002.permS_apply_1, CertificateChecks.Batch11002.permH_word_2, CertificateChecks.Batch11002.permH_word_list_3, CertificateChecks.Batch11002.permH_apply_4, CertificateChecks.Batch11002.permH_word_pow_5, CertificateChecks.Batch11002.permH_conj_6⟩

end Certificates
