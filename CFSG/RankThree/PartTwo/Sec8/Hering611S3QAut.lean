module

public import CFSG.RankThree.PartTwo.KFacts.AutPSL2
import CFSG.LocalAnalysis.ComponentInitial.ScalarSemilinearNormalizer

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.RankThree.PartTwo.KFacts

private theorem psl2FieldAut_mul_comm {K : Type} [Field K] [Finite K] (σ τ : K ≃+* K) :
    psl2FieldAut K σ * psl2FieldAut K τ = psl2FieldAut K τ * psl2FieldAut K σ := by
  rw [← map_mul, ← map_mul, CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm K σ τ]

theorem commutator_mem_pglRange {K : Type} [Field K] [Finite K] (α γ : MulAut (PSL2 K)) :
    α * γ * α⁻¹ * γ⁻¹ ∈ (pglAction K).range := by
  obtain ⟨g, σ, rfl⟩ := exists_pglAction_mul_psl2FieldAut α
  obtain ⟨h, τ, rfl⟩ := exists_pglAction_mul_psl2FieldAut γ
  have hAB := psl2FieldAut_mul_comm σ τ
  have e1 : pglAction K g * psl2FieldAut K σ * (pglAction K h * psl2FieldAut K τ) =
      pglAction K (g * pgl2FieldAut K σ h) * (psl2FieldAut K σ * psl2FieldAut K τ) := by
    rw [map_mul, ← psl2FieldAut_mul_pglAction_mul_inv σ h]
    group
  have e2 : pglAction K h * psl2FieldAut K τ * (pglAction K g * psl2FieldAut K σ) =
      pglAction K (h * pgl2FieldAut K τ g) * (psl2FieldAut K σ * psl2FieldAut K τ) := by
    rw [map_mul, ← psl2FieldAut_mul_pglAction_mul_inv τ g, hAB]
    group
  have hR : pglAction K g * psl2FieldAut K σ * (pglAction K h * psl2FieldAut K τ) *
      (pglAction K g * psl2FieldAut K σ)⁻¹ * (pglAction K h * psl2FieldAut K τ)⁻¹ =
      (pglAction K g * psl2FieldAut K σ * (pglAction K h * psl2FieldAut K τ)) *
        (pglAction K h * psl2FieldAut K τ * (pglAction K g * psl2FieldAut K σ))⁻¹ := by
    group
  refine ⟨(g * pgl2FieldAut K σ h) * (h * pgl2FieldAut K τ g)⁻¹, ?_⟩
  rw [map_mul, map_inv, hR, e1, e2]
  group

theorem conj_mem_pglRange {K : Type} [Field K] [Finite K] (α : MulAut (PSL2 K))
    {p : MulAut (PSL2 K)} (hp : p ∈ (pglAction K).range) : α * p * α⁻¹ ∈ (pglAction K).range := by
  obtain ⟨h, rfl⟩ := hp
  obtain ⟨g, σ, rfl⟩ := exists_pglAction_mul_psl2FieldAut α
  refine ⟨g * pgl2FieldAut K σ h * g⁻¹, ?_⟩
  rw [map_mul, map_mul, map_inv, ← psl2FieldAut_mul_pglAction_mul_inv]
  group

end CFSG.RankThree.PartTwo.Sec8.Hering611
