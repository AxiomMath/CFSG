module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.LinearAlgebra

open LinearMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem prod_surjective_of_linearIndependent {f g : V →ₗ[K] K}
    (h : LinearIndependent K ![f, g]) : Function.Surjective (f.prod g) := by
  rw [← range_eq_top]
  by_contra hne
  obtain ⟨φ, hφ0, hφle⟩ :=
    Submodule.exists_le_ker_of_lt_top (range (f.prod g)) (lt_top_iff_ne_top.mpr hne)
  have hz : ∀ x : V, φ (f x, g x) = 0 := fun x =>
    mem_ker.mp (hφle (mem_range_self (f.prod g) x))
  have hφ : ∀ s t : K, φ (s, t) = s * φ (1, 0) + t * φ (0, 1) := by
    intro s t
    have hst : ((s, t) : K × K) = s • ((1 : K), (0 : K)) + t • ((0 : K), (1 : K)) := by
      ext <;> simp
    rw [hst, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have hzero : φ (1, 0) • f + φ (0, 1) • g = 0 := by
    ext x
    have hx := hz x
    rw [hφ (f x) (g x)] at hx
    rw [add_apply, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul, zero_apply,
      mul_comm (φ (1, 0)) (f x), mul_comm (φ (0, 1)) (g x)]
    exact hx
  obtain ⟨h1, h2⟩ := (LinearIndependent.pair_iff.mp h) (φ (1, 0)) (φ (0, 1)) hzero
  apply hφ0
  refine LinearMap.ext fun x => ?_
  obtain ⟨s, t⟩ := x
  rw [hφ s t, h1, h2, mul_zero, mul_zero, add_zero]
  rfl

theorem prod_surjective_of_not_proportional {f g : V →ₗ[K] K}
    (hf : f ≠ 0) (hg : g ≠ 0) (h : ∀ c : K, f ≠ c • g) :
    Function.Surjective (f.prod g) := by
  apply prod_surjective_of_linearIndependent
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have ht : t = 0 := by
    by_contra ht0
    by_cases hs : s = 0
    · have hg0 : g = 0 := by
        rw [hs, zero_smul, zero_add] at hst
        exact (smul_eq_zero.mp hst).resolve_left ht0
      exact hg hg0
    · have hfg : f = (-(t * s⁻¹)) • g := by
        ext x
        have hx : s * f x + t * g x = 0 := by
          have := congrArg (fun φ : V →ₗ[K] K => φ x) hst
          simpa [add_apply, smul_apply, smul_eq_mul] using this
        have h1 : s * f x = -(t * g x) := add_eq_zero_iff_eq_neg.mp hx
        have h2 : f x = (-(t * g x)) * s⁻¹ := by
          rw [← h1]
          field_simp [hs]
        calc
          f x = (-(t * g x)) * s⁻¹ := h2
          _ = (-(t * s⁻¹)) * g x := by ring
          _ = ((-(t * s⁻¹)) • g) x := by simp [smul_apply, smul_eq_mul]
      exact h (-(t * s⁻¹)) hfg
  subst ht
  have hs : s = 0 := by
    by_contra hs0
    have hf0 : f = 0 := by
      have hst' : s • f = 0 := by simpa using hst
      exact (smul_eq_zero.mp hst').resolve_left hs0
    exact hf hf0
  exact ⟨hs, rfl⟩

theorem prod_surjective_of_not_proportional_zmod {p r : ℕ} [Fact p.Prime]
    (f g : (Fin r → ZMod p) →ₗ[ZMod p] ZMod p)
    (hf : f ≠ 0) (hg : g ≠ 0) (h : ∀ c : ZMod p, f ≠ c • g) :
    Function.Surjective (f.prod g) :=
  prod_surjective_of_not_proportional hf hg h

end CFSG.LinearAlgebra

end
