module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExterior
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd

public section

namespace CFSG.RankThree.PartOne.KCSpComm

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain

section Outside

variable {ℓ f r : ℕ} {K : Type} [Field K]

theorem mem_spSemilinearAutGroup_of_ne_exceptional (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hr : 2 ≤ r)
    (hK : Nat.card K = ℓ ^ f) (hne : ¬(ℓ = 2 ∧ r = 2))
    (α : MulAut (StatedProj (StatedSp r K))) : α ∈ spSemilinearAutGroup r K := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ hf hK
  by_cases hℓ2 : ℓ = 2
  · have hr3 : 3 ≤ r := by omega
    rw [(automorphism_generation (K := K) hr3).1]
    exact Subgroup.mem_top α
  · have hodd : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
    obtain ⟨A, σ, rfl⟩ :=
      CFSG.ComponentClassification.CatalogueBSymplecticRepresentation.automorphism_standard
        hodd hr α
    exact mul_mem (spLinearAutGroup_le_spSemilinearAutGroup (conjAut_mem_spLinearAutGroup A))
      (fieldAut_mem_spSemilinearAutGroup σ)

end Outside

section Transvection

variable {K : Type} [Field K]

@[expose] noncomputable def transvectionT₀ (K : Type) [Field K] : StatedSp 2 K :=
  upperUnipotentSp 2 K (transpose_single_zero_zero (K := K))

theorem exists_subfieldSpHom_eq_transvectionT₀ (k : Subfield K) :
    ∃ g₀ : StatedSp 2 k, subfieldSpHom 2 k g₀ = transvectionT₀ K := by
  refine ⟨upperUnipotentSp 2 k (transpose_single_zero_zero (K := k)), Subtype.ext (Units.ext ?_)⟩
  change spMat (subfieldSpHom 2 k _) = spMat (upperUnipotentSp 2 K _)
  rw [spMat_subfieldSpHom]
  ext p q
  rcases p with p | p <;> rcases q with q | q <;> fin_cases p <;> fin_cases q <;>
    simp [spMat, coe_upperUnipotentSp]

end Transvection

section CharTwo

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem index_spSemilinearAutGroup_two : (spSemilinearAutGroup 2 K).index = 2 := by
  obtain ⟨-, -, -, hEi⟩ :=
    CFSG.ComponentClassification.CatalogueBSymplecticTwo.kernel_generation (K := K)
  have h0 : (spSemilinearAutGroup 2 K).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 : (spSemilinearAutGroup 2 K).index ≠ 1 := by
    intro h
    apply exceptionalAut_not_mem (K := K)
    rw [Subgroup.index_eq_one.mp h]
    exact Subgroup.mem_top _
  omega

theorem not_fixes_transvectionT₀_of_not_mem {β : MulAut (StatedProj (StatedSp 2 K))}
    (hβ : β ∉ spSemilinearAutGroup 2 K) :
    β (proj 2 K (transvectionT₀ K)) ≠ proj 2 K (transvectionT₀ K) := by
  have hEidx := index_spSemilinearAutGroup_two (K := K)
  have hγ : exceptionalAut K ∉ spSemilinearAutGroup 2 K := exceptionalAut_not_mem
  intro hfix
  have h1 : β * (exceptionalAut K)⁻¹ ∈ spSemilinearAutGroup 2 K := by
    rw [Subgroup.mul_mem_iff_of_index_two hEidx]
    exact ⟨fun h => absurd h hβ, fun h => absurd (by simpa using inv_mem h) hγ⟩
  obtain ⟨g, φ, hgφ⟩ := exists_eq_spInner_mul_fieldAut (inv_mem h1)
  have hinvfix : β⁻¹ (proj 2 K (transvectionT₀ K)) = proj 2 K (transvectionT₀ K) := by
    calc β⁻¹ (proj 2 K (transvectionT₀ K)) = β⁻¹ (β (proj 2 K (transvectionT₀ K))) := by
          rw [hfix]
      _ = proj 2 K (transvectionT₀ K) := by
          rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
  have h3 : (β * (exceptionalAut K)⁻¹)⁻¹ (proj 2 K (transvectionT₀ K)) =
      exceptionalAut K (proj 2 K (transvectionT₀ K)) := by
    rw [_root_.mul_inv_rev, inv_inv, MulAut.mul_apply, hinvfix]
  rw [hgφ, spInner_mul_fieldAut_proj, transvectionT₀, exceptionalAut_proj,
    exceptionalSpAut_upperUnipotent] at h3
  have h4 := UnitaryHigher.proj_bijective_of_charTwo.1 h3
  have h5 := displacementInLine_conj g
    (upperUnipotentSp 2 K (transpose_single_zero_zero (K := K))) φ
    displacementInLine_upperUnipotent
  rw [h4] at h5
  exact not_displacementInLine_upperUnipotent_swap h5

end CharTwo

theorem mem_spSemilinearAutGroup_of_fixes_subfield {ℓ f r : ℕ} {K : Type} [Field K]
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hr : 2 ≤ r) (hK : Nat.card K = ℓ ^ f) (k : Subfield K)
    {β : MulAut (StatedProj (StatedSp r K))}
    (h : ∀ g : StatedSp r k,
      β (proj r K (subfieldSpHom r k g)) = proj r K (subfieldSpHom r k g)) :
    β ∈ spSemilinearAutGroup r K := by
  by_cases hcase : ℓ = 2 ∧ r = 2
  · obtain ⟨rfl, rfl⟩ := hcase
    have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
    have : CharP K 2 := finite_field_prime_power_characteristic hℓ hf hK
    by_contra hβ
    obtain ⟨g₀, hg₀⟩ := exists_subfieldSpHom_eq_transvectionT₀ k
    have h0 := h g₀
    rw [hg₀] at h0
    exact not_fixes_transvectionT₀_of_not_mem hβ h0
  · exact mem_spSemilinearAutGroup_of_ne_exceptional hℓ hf hr hK hcase β

end CFSG.RankThree.PartOne.KCSpComm
