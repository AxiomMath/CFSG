module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.Basic

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.Section7

universe v
universe u

@[expose] public def theorem_7_9_statement
    {G : Type u} [Group G] [Finite G]
    (A : Fin 2 → Set G)
    (L : Fin 2 → Subgroup G)
    (H : Fin 2 → Subgroup G)
    (K : Fin 2 → G → Subgroup G)
    (S : (i : Fin 2) → Finset (Section1.ClassFunction (L i)))
    (τ ν : (i : Fin 2) →
      Section1.ClassFunction (L i) →ₗ[ℂ] Section1.ClassFunction G)
    (ζ : (i : Fin 2) → Section1.ClassFunction (L i))
  (β γ : Fin 2 → Section1.ClassFunction G) : Prop :=
  theorem_7_9_source_hypothesis A L H K S τ ν ζ β γ →
    theorem_7_9_parityData β γ →
    (Section1.scalarProduct G (β 0) (γ 1) ≠ 0 ∨
      Section1.scalarProduct G (β 1) (γ 0) ≠ 0)

/-- Peterfalvi `(7.10)`. -/


private theorem theorem_7_9_odd_complex_ne_zero (z : ℤ) :
    (1 : ℂ) + 2 * (z : ℂ) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num at hre
  have hz : ((1 + 2 * z : ℤ) : ℝ) = 0 := by
    norm_num
    linarith
  have hzint : (1 + 2 * z : ℤ) = 0 := by
    exact_mod_cast hz
  omega

private theorem scalarProduct_eq_zero_of_swap_zero
    {G : Type u} [Group G] [Finite G]
    {φ ψ : Section1.ClassFunction G}
    (h : Section1.scalarProduct G φ ψ = 0) :
    Section1.scalarProduct G ψ φ = 0 := by
  have hswap := Section1.scalarProduct_star_swap (G := G) φ ψ
  have hstarzero :
      star (Section1.scalarProduct G ψ φ) = 0 := by
    simpa [h] using hswap
  simpa using congrArg star hstarzero

public theorem theorem_7_9_parityData_of_delta_odd
    {G : Type u} [Group G] [Finite G]
    {β γ : Fin 2 → Section1.ClassFunction G}
    (hγ01 : Section1.scalarProduct G (γ 0) (γ 1) = 0)
    (hγ10 : Section1.scalarProduct G (γ 1) (γ 0) = 0)
    (hodd :
      ∃ z : ℤ,
        Section1.scalarProduct G (γ 0) (β 1 + γ 1) +
            Section1.scalarProduct G (γ 1) (β 0 + γ 0) =
          (1 : ℂ) + 2 * (z : ℂ)) :
    theorem_7_9_parityData β γ := by
  refine ⟨fun i => β i + γ i, ?_, ?_, hodd⟩
  · rw [Section1.scalarProduct_add_left, hγ01]
    ring
  · rw [Section1.scalarProduct_add_left, hγ10]
    ring

public theorem theorem_7_9
    {G : Type u} [Group G] [Finite G]
    (A : Fin 2 → Set G)
    (L : Fin 2 → Subgroup G)
    (H : Fin 2 → Subgroup G)
    (K : Fin 2 → G → Subgroup G)
    (S : (i : Fin 2) → Finset (Section1.ClassFunction (L i)))
    (τ ν : (i : Fin 2) →
      Section1.ClassFunction (L i) →ₗ[ℂ] Section1.ClassFunction G)
    (ζ : (i : Fin 2) → Section1.ClassFunction (L i))
    (β γ : Fin 2 → Section1.ClassFunction G) :
    theorem_7_9_statement A L H K S τ ν ζ β γ := by
  rw [theorem_7_9_statement]
  intro _hsource hparity
  rcases hparity with ⟨Δ, hβ0, hβ1, z, hoddEq⟩
  by_contra hnone
  have hβ0zero : Section1.scalarProduct G (β 0) (γ 1) = 0 := by
    by_contra hne
    exact hnone (Or.inl hne)
  have hβ1zero : Section1.scalarProduct G (β 1) (γ 0) = 0 := by
    by_contra hne
    exact hnone (Or.inr hne)
  have hΔ0γ1 : Section1.scalarProduct G (Δ 0) (γ 1) = 0 := by
    simpa [hβ0zero] using hβ0.symm
  have hΔ1γ0 : Section1.scalarProduct G (Δ 1) (γ 0) = 0 := by
    simpa [hβ1zero] using hβ1.symm
  have hγ1Δ0 : Section1.scalarProduct G (γ 1) (Δ 0) = 0 :=
    scalarProduct_eq_zero_of_swap_zero hΔ0γ1
  have hγ0Δ1 : Section1.scalarProduct G (γ 0) (Δ 1) = 0 :=
    scalarProduct_eq_zero_of_swap_zero hΔ1γ0
  have hbad : (1 : ℂ) + 2 * (z : ℂ) = 0 := by
    rw [hγ0Δ1, hγ1Δ0] at hoddEq
    simpa using hoddEq.symm
  exact theorem_7_9_odd_complex_ne_zero z hbad

end CFSG.Section7
