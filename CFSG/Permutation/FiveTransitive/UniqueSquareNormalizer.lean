module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG

namespace FiveTransitive.UniqueSquareNormalizer

theorem normalizer_centralizes
    {G : Type*} [Group G] (P : Subgroup G) (a : G) (ha : a ∈ P)
    (ha2 : a ^ 2 ≠ 1)
    (hsquares : ∀ x : G, x ∈ P → x ^ 2 = 1 ∨ x ^ 2 = a ^ 2)
    (g : G) (hg : g ∈ Subgroup.normalizer (P : Set G)) :
    g * a ^ 2 = a ^ 2 * g := by
  have hmem : g * a * g⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hg a).mp ha
  have hconj : (g * a * g⁻¹) ^ 2 = g * a ^ 2 * g⁻¹ := by
    rw [conj_pow]
  rcases hsquares _ hmem with h | h
  · rw [hconj] at h
    have h' := congrArg (fun x : G => g⁻¹ * x * g) h
    have : a ^ 2 = 1 := by simpa only [mul_assoc, inv_mul_cancel_left,
      inv_mul_cancel_right, inv_mul_cancel, mul_one, one_mul] using h'
    exact (ha2 this).elim
  · rw [hconj] at h
    exact mul_inv_eq_iff_eq_mul.mp h

theorem le_centralizer
    {G : Type*} [Group G] (P : Subgroup G) (a : G) (ha : a ∈ P)
    (ha2 : a ^ 2 ≠ 1)
    (hsquares : ∀ x : G, x ∈ P → x ^ 2 = 1 ∨ x ^ 2 = a ^ 2) :
    P ≤ Subgroup.centralizer ({a ^ 2} : Set G) := by
  intro g hg
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (normalizer_centralizes P a ha ha2 hsquares g (P.le_normalizer hg))

end FiveTransitive.UniqueSquareNormalizer

end CFSG
