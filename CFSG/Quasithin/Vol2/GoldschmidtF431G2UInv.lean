module

public import CFSG.Quasithin.Vol2.GoldschmidtF431G2UNorm

public noncomputable section

namespace CFSG.Quasithin.H13.F431.G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2

section Squares

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [CharP K 2]

theorem nf_sq (α ρ μ ν β γ : K) :
    nf α ρ μ ν β γ * nf α ρ μ ν β γ =
      nf 0 0 (α * ρ) (α * ρ ^ 2) (α * ρ ^ 3 + ρ ^ 2 * μ + ρ * ν)
        (α * β + α ^ 2 * ρ ^ 3 + ρ * μ ^ 2 + μ * ν) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [nf_mul]
  refine nf_congr ?_ ?_ ?_ ?_ ?_ ?_
  · exact CharTwo.add_self_eq_zero α
  · exact CharTwo.add_self_eq_zero ρ
  · linear_combination μ * h2
  · linear_combination ν * h2
  · linear_combination (β + α * ρ ^ 3) * h2
  · linear_combination (γ + 2 * α * ρ ^ 2 * μ) * h2

theorem nf_sq_eq_one_iff (α ρ μ ν β γ : K) :
    nf α ρ μ ν β γ * nf α ρ μ ν β γ = 1 ↔
      (ρ = 0 ∧ α * β = μ * ν) ∨ (ρ ≠ 0 ∧ α = 0 ∧ ν = ρ * μ) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [nf_sq, ← nf_one, nf_eq_iff]
  constructor
  · rintro ⟨-, -, h1, h3, h4, h5⟩
    by_cases hρ : ρ = 0
    · left
      subst hρ
      refine ⟨rfl, ?_⟩
      have : α * β + μ * ν = 0 := by simpa using h5
      linear_combination this - μ * ν * h2
    · right
      have hα : α = 0 := by
        rcases mul_eq_zero.1 h1 with h | h
        · exact h
        · exact absurd h hρ
      subst hα
      refine ⟨hρ, rfl, ?_⟩
      have h4' : ρ * (ρ * μ + ν) = 0 := by linear_combination h4
      rcases mul_eq_zero.1 h4' with h | h
      · exact absurd h hρ
      · linear_combination h - ρ * μ * h2
  · rintro (⟨hρ, h⟩ | ⟨hρ, hα, hν⟩)
    · subst hρ
      refine ⟨by ring, by ring, by ring, by ring, by ring, ?_⟩
      linear_combination h + μ * ν * h2
    · subst hα
      subst hν
      refine ⟨by ring, by ring, by ring, by ring, ?_, ?_⟩
      · linear_combination (ρ ^ 2 * μ) * h2
      · linear_combination (ρ * μ ^ 2) * h2

end Squares

end CFSG.Quasithin.H13.F431.G2
