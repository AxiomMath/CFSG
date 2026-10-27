module

public import CFSG.Foundations.Basic
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.Quasithin.F112Crit.APrime

open CFSG.Quasithin

variable {G : Type*} [Group G]

structure BenderVertex (H K : Subgroup G) : Prop where
  le : K ≤ H
  normalizes : H ≤ Subgroup.normalizer (K : Set G)
  two_quot : ∀ h ∈ H, ∃ k : ℕ, h ^ 2 ^ k ∈ K
  quasisimple : CFSG.IsQuasisimple (oTwoQuot ↥K)
  odd_center : Odd (Nat.card (Subgroup.center (oTwoQuot ↥K)))
  type : (∃ a : ℕ, 1 ≤ a ∧
      Nonempty (oTwoQuot ↥K ⧸ Subgroup.center (oTwoQuot ↥K) ≃* CFSG.Open.Sz a)) ∨
    (∃ f : ℕ, 2 ≤ f ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (2 ^ f) ^ 2 ∧
      Nonempty (oTwoQuot ↥K ⧸ Subgroup.center (oTwoQuot ↥K) ≃*
        CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ f) F)))

end CFSG.Quasithin.F112Crit.APrime

end
