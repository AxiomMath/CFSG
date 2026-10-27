module

public import CFSG.RankThree.GF2n.Smith81.S81A5Beta

public section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

open scoped commutatorElement

variable (K : Type*) [Field K]

structure InvolModel12 (t : GL (Fin 6) K) : Prop where
  P1 : LinearMap.ker (rho K t - 1) ≤
    Submodule.span K {ξ | ξ ∈ LinearMap.ker (rho K t - 1) ∧ IsPure K ξ}
  QfR : LinearMap.range (rho K t - 1) ≤
    Submodule.span K {ξ | ξ ∈ LinearMap.range (rho K t - 1) ∧
      ∃ p₁ p₂ : Cube K, IsPure K p₁ ∧ IsPure K p₂ ∧ beta K p₁ p₂ = 0 ∧ ξ = p₁ + p₂}
  P3 : ∃ U : Set (GL (Fin 6) K), (∀ u ∈ U, (u : Matrix (Fin 6) (Fin 6) K).det = 1) ∧
    (∀ u ∈ U, u * t = t * u) ∧
    (∀ u ∈ U, ∀ ξ ∈ LinearMap.ker (rho K t - 1), rho K u ξ - ξ ∈ LinearMap.range (rho K t - 1)) ∧
    (∀ ξ ∈ LinearMap.ker (rho K t - 1), (∀ u ∈ U, rho K u ξ = ξ) →
      ξ ∈ LinearMap.range (rho K t - 1))
  P2 : ∃ P : Set (GL (Fin 6) K),
    (∀ u ∈ P, ∃ a b : GL (Fin 6) K, (a : Matrix (Fin 6) (Fin 6) K).det = 1 ∧
      (b : Matrix (Fin 6) (Fin 6) K).det = 1 ∧ a * t = t * a ∧ b * t = t * b ∧ u = ⁅a, b⁆) ∧
    ∀ S : AddSubgroup (Cube K), S ≠ ⊥ → (∀ s ∈ S, s ∈ LinearMap.range (rho K t - 1)) →
      (∀ u ∈ P, ∀ s ∈ S, rho K u s ∈ S) → ∃ p ∈ S, p ≠ 0 ∧ IsPure K p

structure InvolModel3 (t : GL (Fin 6) K) : Prop where
  CR : LinearMap.ker (rho K t - 1) ≤ LinearMap.range (rho K t - 1)
  beta_ne : ∃ p₁ p₂ : Cube K, IsPure K p₁ ∧ IsPure K p₂ ∧
    p₁ + p₂ ∈ LinearMap.range (rho K t - 1) ∧ beta K p₁ p₂ ≠ 0

end CFSG.RankThree.GF2n.Smith81.A5Cube
