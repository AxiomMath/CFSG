module

public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.Bound.Init

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.SU3H1

variable {G H : Type*} [Group G] [Group H]

theorem eq_of_pow_odd_of_map_eq (φ : G →* H) (hker : φ.ker ≤ Subgroup.center G)
    (hsq : ∀ c ∈ φ.ker, c * c = 1) {g₁ g₂ : G} {m₁ m₂ : ℕ} (hm₁ : Odd m₁) (hm₂ : Odd m₂)
    (h₁ : g₁ ^ m₁ = 1) (h₂ : g₂ ^ m₂ = 1) (h : φ g₁ = φ g₂) : g₁ = g₂ := by
  have hc_ker : g₁⁻¹ * g₂ ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  have hc_comm : Commute g₁ (g₁⁻¹ * g₂) :=
    Subgroup.mem_center_iff.mp (hker hc_ker) g₁
  have hc_sq : (g₁⁻¹ * g₂) * (g₁⁻¹ * g₂) = 1 := hsq _ hc_ker
  have hc_m₁ : (g₁⁻¹ * g₂) ^ m₁ = g₁⁻¹ * g₂ := by
    obtain ⟨k, rfl⟩ := hm₁
    rw [pow_succ, pow_mul, sq, hc_sq, one_pow, one_mul]
  have hc_m₂ : (g₁⁻¹ * g₂) ^ m₂ = g₁⁻¹ * g₂ := by
    obtain ⟨k, rfl⟩ := hm₂
    rw [pow_succ, pow_mul, sq, hc_sq, one_pow, one_mul]
  have hg₂ : g₂ = g₁ * (g₁⁻¹ * g₂) := by rw [← mul_assoc, mul_inv_cancel, one_mul]
  have hg₂m : g₂ ^ m₁ = g₁⁻¹ * g₂ := by
    calc g₂ ^ m₁ = (g₁ * (g₁⁻¹ * g₂)) ^ m₁ := congrArg (· ^ m₁) hg₂
      _ = g₁ ^ m₁ * (g₁⁻¹ * g₂) ^ m₁ := hc_comm.mul_pow m₁
      _ = g₁⁻¹ * g₂ := by rw [h₁, one_mul, hc_m₁]
  have hc : g₁⁻¹ * g₂ = 1 := by
    have h3 : g₁⁻¹ * g₂ = (g₂ ^ m₁) ^ m₂ := by rw [← hc_m₂, hg₂m]
    rw [h3, ← pow_mul, mul_comm m₁ m₂, pow_mul, h₂, one_pow]
  exact inv_mul_eq_one.mp hc

theorem exists_pow_odd_lift (φ : G →* H) (hφ : Function.Surjective φ)
    (hsq : ∀ c ∈ φ.ker, c * c = 1) {h : H} {m : ℕ} (hm : Odd m) (hh : h ^ m = 1) :
    ∃ g : G, φ g = h ∧ g ^ m = 1 := by
  obtain ⟨g, hg⟩ := hφ h
  refine ⟨g ^ (m + 1), ?_, ?_⟩
  · rw [map_pow, hg, pow_succ, hh, one_mul]
  · have hgm : g ^ m ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_pow, hg, hh]
    have hsqm : (g ^ m) * (g ^ m) = 1 := hsq _ hgm
    obtain ⟨k, hk⟩ := hm
    have heven : (g ^ m) ^ (m + 1) = 1 := by
      rw [show m + 1 = 2 * (k + 1) by omega, pow_mul, sq, hsqm, one_pow]
    rw [← pow_mul, mul_comm (m + 1) m, pow_mul]
    exact heven

theorem commute_of_map_commute_of_pow_odd (φ : G →* H) (hker : φ.ker ≤ Subgroup.center G)
    (hsq : ∀ c ∈ φ.ker, c * c = 1) {g g₂ : G} {m : ℕ} (hm : Odd m) (h₂ : g₂ ^ m = 1)
    (h : Commute (φ g) (φ g₂)) : Commute g g₂ := by
  have hconj : (g * g₂ * g⁻¹) ^ m = 1 := by
    rw [conj_pow, h₂, mul_one, mul_inv_cancel]
  have hmap : φ (g * g₂ * g⁻¹) = φ g₂ := by
    rw [map_mul, map_mul, map_inv, h.eq, mul_assoc, mul_inv_cancel, mul_one]
  have h1 : g * g₂ * g⁻¹ = g₂ :=
    eq_of_pow_odd_of_map_eq φ hker hsq hm hm hconj h₂ hmap
  exact mul_inv_eq_iff_eq_mul.mp h1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.SU3H1
