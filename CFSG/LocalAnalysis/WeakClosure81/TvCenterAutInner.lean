module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.WeakClosure81.FieldInnerTransvection
public import CFSG.LocalAnalysis.WeakClosure81.InnerFieldDualTransvection

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix
open CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.CGT.Timmesfeld75

variable {K : Type*} [Field K]

theorem eq_conjAut_of_fixes_tvCenter [Finite K] {n : ℕ} (hn : 3 ≤ n)
    {a : Fin n → K} (ha : a ≠ 0) (α : MulAut (projectiveSL n K))
    (hfix : ∀ (f : Fin n → K) (hf : f ⬝ᵥ a = 0),
      α (proj n K (tvSL a f hf)) = proj n K (tvSL a f hf)) :
    ∃ A : GL (Fin n) K, α = conjAut n K A := by
  obtain ⟨A, σ, ε, hε, hα⟩ := (automorphism_generation (K := K) hn).2 α
  rcases Nat.eq_zero_or_pos ε with h0 | hpos
  · subst h0
    have hfix' : ∀ (f : Fin n → K) (hf : f ⬝ᵥ a = 0),
        (conjAut n K A * fieldAut n K σ) (proj n K (tvSL a f hf)) =
          proj n K (tvSL a f hf) := by
      intro f hf
      have h := hfix f hf
      rwa [hα, pow_zero, mul_one] at h
    have hσ : σ = 1 :=
      fieldAut_eq_one_of_conjAut_mul_fixes_tvCenter hn ha A σ hfix'
    refine ⟨A, ?_⟩
    rw [hα, pow_zero, mul_one, hσ, map_one, mul_one]
  · have h1 : ε = 1 := by omega
    subst h1
    have hfix' : ∀ (f : Fin n → K) (hf : f ⬝ᵥ a = 0),
        (conjAut n K A * fieldAut n K σ * dualAut n K) (proj n K (tvSL a f hf)) =
          proj n K (tvSL a f hf) := by
      intro f hf
      have h := hfix f hf
      rwa [hα, pow_one] at h
    exact False.elim
      (conjAut_mul_fieldAut_mul_dualAut_ne_of_fixes_tvCenter hn ha A σ hfix')

end CFSG.LocalAnalysis.WeakClosure81
