module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartOne.S12.Hyp
public import CFSG.RankThree.PartOne.S15K.ReflGroup
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.PartOne.S15K

open CFSG CFSG.RankThree.PartOne CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory

theorem perm4_pow_twelve : ∀ x : Equiv.Perm (Fin 4), x ^ 12 = 1 := by decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
theorem r2s4_pow_twelve : ∀ x : R2S4, x ^ 12 = 1 := by decide +kernel

variable {G : Type} [Group G]

theorem reflectionGroup_pow_twelve {p : ℕ} {E : Subgroup G}
    (h : Nonempty (↥(reflectionGroup p E) ≃* Equiv.Perm (Fin 4)) ∨
      Nonempty (↥(reflectionGroup p E) ≃* R2S4)) : ∀ x ∈ reflectionGroup p E, x ^ 12 = 1 := by
  intro x hx
  have key : ∀ {D : Type} [Group D], (↥(reflectionGroup p E) ≃* D) → (∀ d : D, d ^ 12 = 1) →
      x ^ 12 = 1 := by
    intro D _ e hD
    have h2 : (⟨x, hx⟩ : ↥(reflectionGroup p E)) ^ 12 = 1 := by
      apply e.injective
      rw [map_pow, map_one]
      exact hD _
    simpa using congrArg Subtype.val h2
  rcases h with h | h
  · obtain ⟨e⟩ := h
    exact key e perm4_pow_twelve
  · obtain ⟨e⟩ := h
    exact key e r2s4_pow_twelve

theorem false_of_dihedral_eight {M : Type*} [Group M] {Γ R : Subgroup M} (hΓR : Γ ≤ R)
    (hR : ∀ x ∈ R, x ^ 12 = 1) (e : ↥Γ ≃* DihedralGroup 8) : False := by
  set y : ↥Γ := e.symm (DihedralGroup.r 1) with hy
  have h8 : orderOf y = 8 := by
    rw [hy, MulEquiv.orderOf_eq]
    exact DihedralGroup.orderOf_r_one
  have h8' : orderOf (y : M) = 8 := by rw [Subgroup.orderOf_coe]; exact h8
  have h12 : (y : M) ^ 12 = 1 := hR _ (hΓR y.2)
  have := orderOf_dvd_of_pow_eq_one h12
  rw [h8'] at this
  omega

variable [Finite G]

end CFSG.RankThree.PartOne.S15K
