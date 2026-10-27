module

public import CFSG.Timmesfeld.Bridge.LocalA

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

variable {G : Type*} [Group G] {D : Set G}

theorem commute_of_perfect {X : Subgroup G} (hX : ⁅X, X⁆ = X) {n : G}
    (hc : ∀ x ∈ X, ∀ y ∈ X, Commute (x * n * x⁻¹ * n⁻¹) y)
    (hab : ∀ x ∈ X, ∀ y ∈ X, Commute (x * n * x⁻¹ * n⁻¹) (y * n * y⁻¹ * n⁻¹)) :
    ∀ x ∈ X, Commute x n := by
  have hmul : ∀ x ∈ X, ∀ y ∈ X, (x * y) * n * (x * y)⁻¹ * n⁻¹ =
      (x * n * x⁻¹ * n⁻¹) * (y * n * y⁻¹ * n⁻¹) := by
    intro x hx y hy
    have h1 : (x * y) * n * (x * y)⁻¹ * n⁻¹ =
        (x * (y * n * y⁻¹ * n⁻¹) * x⁻¹) * (x * n * x⁻¹ * n⁻¹) := by group
    have h2 : x * (y * n * y⁻¹ * n⁻¹) * x⁻¹ = y * n * y⁻¹ * n⁻¹ := by
      rw [← (hc y hy x hx).eq, mul_inv_cancel_right]
    rw [h1, h2]
    exact (hab y hy x hx).eq
  have hone : (1 : G) * n * (1 : G)⁻¹ * n⁻¹ = 1 := by group
  have hinv : ∀ x ∈ X, x⁻¹ * n * x⁻¹⁻¹ * n⁻¹ = (x * n * x⁻¹ * n⁻¹)⁻¹ := by
    intro x hx
    have h1 := hmul x hx _ (X.inv_mem hx)
    rw [mul_inv_cancel, hone] at h1
    exact eq_inv_of_mul_eq_one_right h1.symm
  have hcomm : ⁅X, X⁆ ≤ Subgroup.centralizer {n} := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxy : (x * y * x⁻¹ * y⁻¹) * n * (x * y * x⁻¹ * y⁻¹)⁻¹ * n⁻¹ = 1 := by
      rw [hmul _ (X.mul_mem (X.mul_mem hx hy) (X.inv_mem hx)) _ (X.inv_mem hy),
        hmul _ (X.mul_mem hx hy) _ (X.inv_mem hx), hmul _ hx _ hy, hinv _ hx, hinv _ hy,
        (hab x hx y hy).eq]
      group
    rw [commutatorElement_def]
    have h2 := mul_inv_eq_one.1 hxy
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2
  intro x hx
  have hx' : x ∈ ⁅X, X⁆ := by rw [hX]; exact hx
  have := hcomm hx'
  rw [Subgroup.mem_centralizer_singleton_iff] at this
  exact this

variable {K : Type*} [Field K]

end CFSG.Timmesfeld.Bridge
