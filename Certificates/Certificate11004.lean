module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizersInputs
public import Certificates.Certificate11003

public section

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.M12Cover CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.OuterAutomorphisms

namespace CertificateChecks.Batch11004

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.M12Cover CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.OuterAutomorphisms

private theorem m12Rep1_eq_0 : m12Rep1 = m12gA := by
  decide +kernel

private theorem gz_conj_1 : permZ = evalCodes [m12gA, m12gB] gzWord * m12Rep2 *
    (evalCodes [m12gA, m12gB] gzWord)⁻¹ := by
  decide +kernel

private theorem permA0_conj_2 : permA0 = permG0 * m12gA * permG0⁻¹ := by
  decide +kernel

private theorem permA1_conj_3 : permA1 = permG1 * permZ * permG1⁻¹ := by
  decide +kernel

private theorem permA0_apply_4 : ∀ i, permA0 i = ![0, 1, 11, 4, 3, 5, 6, 10, 9, 8, 7, 2] i := by
  decide +kernel

private theorem permA1_apply_5 : ∀ i, permA1 i = ![1, 0, 3, 2, 11, 6, 5, 8, 7, 10, 9, 4] i := by
  decide +kernel

end CertificateChecks.Batch11004

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.M12Cover CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.OuterAutomorphisms in
theorem certificate11004 : (
m12Rep1 = m12gA
)
    ∧ (
permZ = evalCodes [m12gA, m12gB] gzWord * m12Rep2 *
    (evalCodes [m12gA, m12gB] gzWord)⁻¹
)
    ∧ (
permA0 = permG0 * m12gA * permG0⁻¹
)
    ∧ (
permA1 = permG1 * permZ * permG1⁻¹
)
    ∧ (
∀ i, permA0 i = ![0, 1, 11, 4, 3, 5, 6, 10, 9, 8, 7, 2] i
)
    ∧ (
∀ i, permA1 i = ![1, 0, 3, 2, 11, 6, 5, 8, 7, 10, 9, 4] i
) := by
  exact ⟨CertificateChecks.Batch11004.m12Rep1_eq_0, CertificateChecks.Batch11004.gz_conj_1, CertificateChecks.Batch11004.permA0_conj_2, CertificateChecks.Batch11004.permA1_conj_3, CertificateChecks.Batch11004.permA0_apply_4, CertificateChecks.Batch11004.permA1_apply_5⟩

end Certificates
