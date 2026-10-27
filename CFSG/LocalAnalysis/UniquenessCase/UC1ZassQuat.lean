module

public import CFSG.LocalAnalysis.UniquenessCase.UC1ZassPlane
public import Mathlib.GroupTheory.SpecificGroups.Quaternion

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.Zass

open QuaternionGroup

section Quat

variable {K : Type*} [Field K] {M : Type*} [AddCommGroup M] [Module K M] {G : Type*} [Group G]

theorem quaternion_a_eq_pow {t : ℕ} (i : ZMod (2 * 2 ^ t)) :
    (a i : QuaternionGroup (2 ^ t)) = a 1 ^ i.val := by
  rw [a_one_pow, ZMod.natCast_zmod_val]

theorem quaternion_xa_eq_pow_mul {t : ℕ} (i : ZMod (2 * 2 ^ t)) :
    (xa i : QuaternionGroup (2 ^ t)) = a 1 ^ (-i).val * xa 0 := by
  rw [a_one_pow, ZMod.natCast_zmod_val, a_mul_xa]
  simp

theorem quaternion_xa_conj_a {N : ℕ} :
    (xa 0 : QuaternionGroup N) * a 1 * (xa 0)⁻¹ = (a 1)⁻¹ := by
  rw [mul_inv_eq_iff_eq_mul]
  have h1 : (a 1 : QuaternionGroup N)⁻¹ = a (-1) :=
    inv_eq_of_mul_eq_one_right (by simp)
  rw [h1]
  simp

theorem exists_plane_of_quaternion (ρ : Representation K G M) [Nontrivial M] (hk : (2 : K) ≠ 0)
    {t : ℕ} (ht : 1 ≤ t) {ζ : K} (hζ : IsPrimitiveRoot ζ (2 ^ (t + 1)))
    {φ : QuaternionGroup (2 ^ t) →* G} (hφ : Function.Injective φ)
    (hz : ∀ v : M, ρ (φ (a ((2 ^ t : ℕ) : ZMod (2 * 2 ^ t)))) v = -v) :
    ∃ W : Submodule K M, Module.finrank K W = 2 ∧
      (∀ g : QuaternionGroup (2 ^ t), ∀ x ∈ W, ρ (φ g) x ∈ W) ∧
      ∀ g : QuaternionGroup (2 ^ t), (∃ μ : K, ∀ x ∈ W, ρ (φ g) x = μ • x) →
        g = 1 ∨ g = a ((2 ^ t : ℕ) : ZMod (2 * 2 ^ t)) := by
  have hc : φ (a 1) ^ 2 ^ (t + 1) = 1 := by
    rw [← map_pow, pow_succ', a_one_pow_n, map_one]
  have hy : φ (xa 0) * φ (a 1) * (φ (xa 0))⁻¹ = (φ (a 1))⁻¹ := by
    rw [← map_mul, ← map_inv, ← map_mul, ← map_inv, quaternion_xa_conj_a]
  have hy2 : φ (xa 0) ^ 2 = φ (a 1) ^ 2 ^ t := by
    rw [← map_pow, ← map_pow, xa_sq, a_one_pow]
  have hz' : ∀ v : M, ρ (φ (a 1) ^ 2 ^ t) v = -v := by
    intro v
    rw [← map_pow, a_one_pow]
    exact hz v
  obtain ⟨W, hW, hWc, hWy, hsc, hsy⟩ := exists_plane ρ hk ht hζ hc hy hy2 hz'
  have hpow : ∀ k : ℕ, ∀ x ∈ W, ρ (φ (a 1) ^ k) x ∈ W := by
    intro k
    induction k with
    | zero => intro x hx; simpa using hx
    | succ k ih =>
      intro x hx
      rw [pow_succ, map_mul, Module.End.mul_apply]
      exact ih _ (hWc x hx)
  refine ⟨W, hW, ?_, ?_⟩
  · intro g x hx
    cases g with
    | a i =>
      rw [quaternion_a_eq_pow i, map_pow]
      exact hpow _ x hx
    | xa i =>
      rw [quaternion_xa_eq_pow_mul i, map_mul, map_pow, map_mul, Module.End.mul_apply]
      exact hpow _ _ (hWy x hx)
  · intro g hg
    cases g with
    | a i =>
      have hg' : ∃ μ : K, ∀ x ∈ W, ρ (φ (a 1) ^ i.val) x = μ • x := by
        rw [quaternion_a_eq_pow i, map_pow] at hg
        exact hg
      rcases hsc _ hg' with h | h
      · left
        rw [quaternion_a_eq_pow i]
        exact hφ (by rw [map_pow, h, map_one])
      · right
        rw [quaternion_a_eq_pow i]
        have h2 : (a 1 : QuaternionGroup (2 ^ t)) ^ i.val = a 1 ^ 2 ^ t :=
          hφ (by rw [map_pow, map_pow, h])
        rw [h2, a_one_pow]
    | xa i =>
      rw [quaternion_xa_eq_pow_mul i, map_mul, map_pow] at hg
      exact absurd hg (hsy _)

end Quat

end CFSG.LocalAnalysis.UniquenessCase.UCK.Zass
