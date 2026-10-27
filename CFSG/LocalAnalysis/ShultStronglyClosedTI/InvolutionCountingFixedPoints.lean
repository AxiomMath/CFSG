module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.InvolutionCountingClassClosure

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.InvolutionCounting

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]

theorem conj_smul_eq_self_iff {x : G} {α : Ω} (hx : ∀ β : Ω, x • β = β ↔ β = α) (k : G)
    (β : Ω) : (k * x * k⁻¹) • β = β ↔ β = k • α := by
  rw [mul_smul, mul_smul, smul_eq_iff_eq_inv_smul, hx, inv_smul_eq_iff]

theorem smul_eq_self_of_commute {x y : G} {γ : Ω} (hxy : Commute x y)
    (hy : ∀ β : Ω, y • β = β ↔ β = γ) : x • γ = γ := by
  refine (hy (x • γ)).mp ?_
  rw [← mul_smul, ← hxy.eq, mul_smul, (hy γ).mpr rfl]

theorem exists_isConj_commute_mul_smul_eq_self [Finite G] (htrans : MulAction.IsPretransitive G Ω)
    {α β : Ω} (hβ : β ≠ α) {z w : G} (hz : z * z = 1) (hw : w * w = 1) (hzw : ¬ IsConj z w)
    (hzfix : ∀ γ : Ω, z • γ = γ ↔ γ = α) (hwfix : ∀ γ : Ω, w • γ = γ ↔ γ = α)
    (hcomm : ∀ r s : G, IsConj z r → IsConj z s → Even (orderOf (r * s)) → Commute r s)
    (hprod : ∀ r s : G, IsConj z r → IsConj z s → r ≠ s → Commute r s → IsConj z (r * s)) :
    ∃ r : G, IsConj z r ∧ r • α = α ∧ Commute w r ∧ ∃ γ : Ω, γ ≠ α ∧ (w * r) • γ = γ := by
  obtain ⟨g, hg⟩ := htrans.exists_smul_eq α β
  have hs : IsConj z (g * z * g⁻¹) := isConj_iff.mpr ⟨g, rfl⟩
  have hsfix : ∀ γ : Ω, (g * z * g⁻¹) • γ = γ ↔ γ = β := fun γ =>
    hg ▸ conj_smul_eq_self_iff hzfix g γ
  have hDfix : ∀ x : G, IsConj z x → ∃ γ : Ω, ∀ δ : Ω, x • δ = δ ↔ δ = γ := by
    intro x hx
    obtain ⟨k, rfl⟩ := isConj_iff.mp hx
    exact ⟨k • α, conj_smul_eq_self_iff hzfix k⟩
  have hs2 := mul_self_eq_one_of_isConj hz hs
  obtain ⟨d, hd0, hd⟩ := exists_orderOf_mul_eq_two_mul hw hs2
    fun h => hzw (hs.trans (isConj_comm.mp h))
  have ha2 : (w * (g * z * g⁻¹)) ^ d * (w * (g * z * g⁻¹)) ^ d = 1 :=
    mul_self_eq_one_of_orderOf_eq_two (orderOf_pow_half hd hd0)
  have hwa := commute_of_mem_zpowers (conj_mul_left_eq_inv hw hs2)
    (Subgroup.npow_mem_zpowers _ d) ha2
  have hsa := commute_of_mem_zpowers (conj_mul_right_eq_inv hw hs2)
    (Subgroup.npow_mem_zpowers _ d) ha2
  rcases Nat.even_or_odd d with heven | hodd
  · obtain ⟨rfl, hsq⟩ := eq_two_and_isConj_sq_of_even hz hw hs hcomm hprod hd hd0 heven
    obtain ⟨γ, hγ⟩ := hDfix _ hsq
    exact absurd (((hsfix γ).mp (smul_eq_self_of_commute hsa hγ)).symm.trans
      ((hwfix γ).mp (smul_eq_self_of_commute hwa hγ))) hβ
  · obtain ⟨hr, hrw⟩ := isConj_pow_mul_and_commute_of_odd hz hw hs hd hodd
    obtain ⟨γ, hγ⟩ := hDfix _ hr
    rw [(hwfix γ).mp (smul_eq_self_of_commute hrw.symm hγ)] at hγ
    have hrα := (hγ α).mpr rfl
    have hwr : w * ((w * (g * z * g⁻¹)) ^ d * w) = (w * (g * z * g⁻¹)) ^ d := by
      rw [← mul_assoc, hwa.eq, mul_assoc, hw, mul_one]
    have haα : (w * (g * z * g⁻¹)) ^ d • α = α := by
      rw [← hwr, mul_smul, hrα, (hwfix α).mpr rfl]
    refine ⟨_, hr, hrα, hrw.symm, (g * z * g⁻¹) • α, fun h => hβ ((hsfix α).mp h).symm, ?_⟩
    rw [hwr, ← mul_smul, ← hsa.eq, mul_smul, haα]

end CFSG.ShultStronglyClosedTI.InvolutionCounting
