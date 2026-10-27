module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAut
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutFixedData

public section

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.M12Cover CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier CFSG.ComponentClassification.OuterAutomorphisms commutatorElement

namespace CertificateChecks.Batch11003

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.M12Cover CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier CFSG.ComponentClassification.OuterAutomorphisms commutatorElement

private theorem pairs_permX_0 : evalCodes [m12gA, m12gB] wordX = permX := by
  decide +kernel

private theorem pairs_permX_1 : evalCodes [m12gA, m12bp] wordX = permX := by
  decide +kernel

private theorem pairs_permY_2 : evalCodes [m12gA, m12gB] wordY = permY := by
  decide +kernel

private theorem pairs_permY_3 : evalCodes [m12gA, m12bp] wordY = permY := by
  decide +kernel

private theorem pairs_permZ_4 : evalCodes [m12gA, m12gB] wordZ = permZ := by
  decide +kernel

private theorem pairs_permZ_5 : evalCodes [m12gA, m12bp] wordZ = permZ := by
  decide +kernel

private theorem permX_apply_6 : ∀ i, permX i = ![0, 3, 8, 6, 10, 1, 11, 2, 4, 9, 7, 5] i := by
  decide +kernel

private theorem permY_apply_7 : ∀ i, permY i = ![6, 0, 2, 3, 7, 11, 5, 9, 10, 8, 4, 1] i := by
  decide +kernel

private theorem permZ_apply_8 : ∀ i, permZ i = ![9, 7, 3, 2, 11, 10, 8, 1, 6, 0, 5, 4] i := by
  decide +kernel

private theorem permZ_sq_9 : permZ ^ 2 = 1 := by
  decide +kernel

private theorem fourGroupArrays_sorted_10 : (∀ i, (fourGroupArrays i).Pairwise (· < ·)) ∧
      (List.ofFn fourGroupArrays).Pairwise (· < ·) := by
  decide +kernel

private theorem fivePointHom_mem_11 : permX ^ 5 = 1 := by
  decide +kernel

private theorem fivePointHom_mem_12 : permY ^ 5 = 1 := by
  decide +kernel

private theorem permX_comm_permZ_13 : permX * permZ = permZ * permX := by
  decide +kernel

private theorem permY_comm_permZ_14 : permY * permZ = permZ * permY := by
  decide +kernel

private theorem permX_commutator_15 : permX = permY⁻¹ * (permY⁻¹ * permX⁻¹) * permY⁻¹⁻¹ * (permY⁻¹ * permX⁻¹)⁻¹ := by
  decide +kernel

private theorem permY_commutator_16 : permY = permX⁻¹ * (permX⁻¹ * permY⁻¹) * permX⁻¹⁻¹ * (permX⁻¹ * permY⁻¹)⁻¹ := by
  decide +kernel

end CertificateChecks.Batch11003

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.M12Cover CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier CFSG.ComponentClassification.OuterAutomorphisms commutatorElement in
theorem certificate11003 : (
evalCodes [m12gA, m12gB] wordX = permX
)
    ∧ (
evalCodes [m12gA, m12bp] wordX = permX
)
    ∧ (
evalCodes [m12gA, m12gB] wordY = permY
)
    ∧ (
evalCodes [m12gA, m12bp] wordY = permY
)
    ∧ (
evalCodes [m12gA, m12gB] wordZ = permZ
)
    ∧ (
evalCodes [m12gA, m12bp] wordZ = permZ
)
    ∧ (
∀ i, permX i = ![0, 3, 8, 6, 10, 1, 11, 2, 4, 9, 7, 5] i
)
    ∧ (
∀ i, permY i = ![6, 0, 2, 3, 7, 11, 5, 9, 10, 8, 4, 1] i
)
    ∧ (
∀ i, permZ i = ![9, 7, 3, 2, 11, 10, 8, 1, 6, 0, 5, 4] i
)
    ∧ (
permZ ^ 2 = 1
)
    ∧ (
(∀ i, (fourGroupArrays i).Pairwise (· < ·)) ∧
      (List.ofFn fourGroupArrays).Pairwise (· < ·)
)
    ∧ (
permX ^ 5 = 1
)
    ∧ (
permY ^ 5 = 1
)
    ∧ (
permX * permZ = permZ * permX
)
    ∧ (
permY * permZ = permZ * permY
)
    ∧ (
permX = permY⁻¹ * (permY⁻¹ * permX⁻¹) * permY⁻¹⁻¹ * (permY⁻¹ * permX⁻¹)⁻¹
)
    ∧ (
permY = permX⁻¹ * (permX⁻¹ * permY⁻¹) * permX⁻¹⁻¹ * (permX⁻¹ * permY⁻¹)⁻¹
) := by
  exact ⟨CertificateChecks.Batch11003.pairs_permX_0, CertificateChecks.Batch11003.pairs_permX_1, CertificateChecks.Batch11003.pairs_permY_2, CertificateChecks.Batch11003.pairs_permY_3, CertificateChecks.Batch11003.pairs_permZ_4, CertificateChecks.Batch11003.pairs_permZ_5, CertificateChecks.Batch11003.permX_apply_6, CertificateChecks.Batch11003.permY_apply_7, CertificateChecks.Batch11003.permZ_apply_8, CertificateChecks.Batch11003.permZ_sq_9, CertificateChecks.Batch11003.fourGroupArrays_sorted_10, CertificateChecks.Batch11003.fivePointHom_mem_11, CertificateChecks.Batch11003.fivePointHom_mem_12, CertificateChecks.Batch11003.permX_comm_permZ_13, CertificateChecks.Batch11003.permY_comm_permZ_14, CertificateChecks.Batch11003.permX_commutator_15, CertificateChecks.Batch11003.permY_commutator_16⟩

end Certificates
