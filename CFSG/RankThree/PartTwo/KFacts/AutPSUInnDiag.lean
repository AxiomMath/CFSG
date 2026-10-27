module

public import CFSG.Milestones.ASVolI.A2OddAut

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.ASVolI CFSG.ASVolI.ChA CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag

theorem map_range_psuConj_le_innDiagSubgroup {X : Type} [Group X] {n : ℕ} {K : Type}
    [Field K] (hu : UnitaryFieldData 2 n K) (e : X ≃* unitaryPSU hu 3) :
    (psuConj hu).range.map (MulAut.congr e.symm).toMonoidHom ≤ innDiagSubgroup X := by
  haveI : Finite K := hu.finite
  rintro _ ⟨A, ⟨a, rfl⟩, rfl⟩
  refine Subgroup.subset_closure (show IsInnDiagAut X _ from Or.inr (Or.inr ?_))
  refine ⟨n, K, inferInstance, inferInstance, e.trans
    (unitaryPSUEquiv hu (by norm_num : 1 ≤ 3)), (a : GL (Fin 3) K), ?_, ?_⟩
  · rw [hu.card, mul_comm 2 n, pow_mul]
  · have h1 := burnsideA26_isProjConjAut_u3 hu
      (e.trans (unitaryPSUEquiv hu (by norm_num : 1 ≤ 3))) a
    have h2 : MulAut.congr ((e.trans (unitaryPSUEquiv hu (by norm_num : 1 ≤ 3))).trans
        (unitaryPSUEquiv hu (by norm_num : 1 ≤ 3)).symm).symm (psuConj hu a) =
        MulAut.congr e.symm (psuConj hu a) := by
      ext x
      simp [MulAut.congr_apply]
    rwa [h2] at h1

theorem commutator_mem_range_psuConj {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (hq : 2 < p ^ f) (α β : MulAut (unitaryPSU h 3)) :
    α * β * α⁻¹ * β⁻¹ ∈ (psuConj h).range := by
  haveI : Finite K := h.finite
  haveI : (psuConj h).range.Normal := (stdPinnedPSU3_stable (h := h) hq).normal
  obtain ⟨A, σ, rfl⟩ := exists_psuConj_mul_psuField hq α
  obtain ⟨B, τ, rfl⟩ := exists_psuConj_mul_psuField hq β
  have hqA : QuotientGroup.mk' (psuConj h).range (psuConj h A) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨A, rfl⟩
  have hqB : QuotientGroup.mk' (psuConj h).range (psuConj h B) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨B, rfl⟩
  have hcomm : ∀ σ τ : K ≃+* K,
      psuField h σ * psuField h τ = psuField h τ * psuField h σ := fun σ τ => by
    conv_lhs => rw [← map_mul]
    conv_rhs => rw [← map_mul]
    rw [ringAut_mul_comm K σ τ]
  apply (QuotientGroup.eq_one_iff _).mp
  change QuotientGroup.mk' (psuConj h).range
    ((psuConj h A * psuField h σ) * (psuConj h B * psuField h τ) *
      (psuConj h A * psuField h σ)⁻¹ * (psuConj h B * psuField h τ)⁻¹) = 1
  simp only [map_mul, map_inv, hqA, hqB, one_mul]
  rw [show QuotientGroup.mk' (psuConj h).range (psuField h σ) *
      QuotientGroup.mk' (psuConj h).range (psuField h τ) *
      (QuotientGroup.mk' (psuConj h).range (psuField h σ))⁻¹ *
      (QuotientGroup.mk' (psuConj h).range (psuField h τ))⁻¹ = 1 by
    rw [show QuotientGroup.mk' (psuConj h).range (psuField h σ) *
        QuotientGroup.mk' (psuConj h).range (psuField h τ) =
        QuotientGroup.mk' (psuConj h).range (psuField h τ) *
        QuotientGroup.mk' (psuConj h).range (psuField h σ) by
      conv_lhs => rw [← map_mul]
      conv_rhs => rw [← map_mul]
      rw [hcomm σ τ]]
    group]

end CFSG.RankThree.PartTwo.KFacts

end
