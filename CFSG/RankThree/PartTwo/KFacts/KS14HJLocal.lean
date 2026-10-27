module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS14

open CFSG CFSG.Blueprint CFSG.RankThree.PartTwo

variable {X : Type} [Group X] [Finite X]

theorem j2_le_normalizer_of_card_nine (h415 : Sec4.Item4_15)
    (hX : Nonempty (X ≃* NativeSporadic.J2)) (P : Sylow 3 X) {A : Subgroup X}
    (hAP : A ≤ P) (hA9 : Nat.card A = 9) :
    (P : Subgroup X) ≤ Subgroup.normalizer (A : Set X) := by
  obtain ⟨⟨hHeis, -⟩, -⟩ := h415 X hX P _ rfl _ rfl
  obtain ⟨-, h27, -⟩ := hHeis
  set A' := A.subgroupOf (P : Subgroup X) with hA'
  have hA'9 : Nat.card A' = 9 := by
    rw [hA', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAP).toEquiv, hA9]
  have hidx : A'.index = 3 := by
    have h := A'.card_mul_index
    rw [hA'9, h27] at h
    omega
  have hnorm : A'.Normal := Subgroup.normal_of_index_eq_minFac_card (by
    rw [hidx, h27]
    norm_num)
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hAP).mp hnorm

theorem j2_maxInvariant_two_ncard (h415 : Sec4.Item4_15)
    (hX : Nonempty (X ≃* NativeSporadic.J2)) (P : Sylow 3 X) {A : Subgroup X}
    (hAP : A ≤ P) (hA9 : Nat.card A = 9) :
    (maxInvariantPiSubgroups ⊤ A (piOf 2)).ncard = 3 := by
  obtain ⟨-, -, -, -, h5⟩ := h415 X hX P _ rfl _ rfl
  obtain ⟨S, -, -, hS3, -⟩ := h5 A ⟨hAP, hA9⟩
  exact hS3

theorem j2_maxInvariant_two_transitive (h415 : Sec4.Item4_15)
    (hX : Nonempty (X ≃* NativeSporadic.J2)) (P : Sylow 3 X) {A : Subgroup X}
    (hAP : A ≤ P) (hA9 : Nat.card A = 9) {U₁ U₂ : Subgroup X}
    (hU₁ : U₁ ∈ maxInvariantPiSubgroups ⊤ A (piOf 2))
    (hU₂ : U₂ ∈ maxInvariantPiSubgroups ⊤ A (piOf 2)) :
    ∃ x ∈ (P : Subgroup X), x ∈ Subgroup.normalizer (A : Set X) ∧ U₂ = conjugate U₁ x := by
  obtain ⟨-, -, -, -, h5⟩ := h415 X hX P _ rfl _ rfl
  obtain ⟨S, -, hSP, -⟩ := h5 A ⟨hAP, hA9⟩
  rw [hSP] at hU₁ hU₂
  obtain ⟨y₁, hy₁, rfl⟩ := hU₁
  obtain ⟨y₂, hy₂, rfl⟩ := hU₂
  have hN := j2_le_normalizer_of_card_nine h415 hX P hAP hA9
  refine ⟨y₁⁻¹ * y₂, mul_mem (inv_mem hy₁) hy₂, hN (mul_mem (inv_mem hy₁) hy₂), ?_⟩
  rw [conjugate_conjugate_eq_mul, mul_inv_cancel_left]

end CFSG.RankThree.PartTwo.KFacts.KS14
