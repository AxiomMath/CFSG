module

public import CFSG.Quasithin.Background.A4Defs
public import CFSG.CharacterTheory.PSL2Table.Basic

public section

namespace CFSG.Quasithin

open CFSG.PSL2Table
open scoped MatrixGroups

theorem mk_injective_of_charTwo1521 {K : Type} [Field K] [CharP K 2] :
    Function.Injective (mk : SL(2, K) →* PSL(2, K)) := by
  intro A B h
  rcases (CFSG.PSL2Table.mk_eq_mk_iff A B).1 h with h | h
  · exact h.symm
  · have hneg : -A = A := by
      apply CFSG.PSL2Table.SL_ext <;> simp [CharTwo.neg_eq]
    rw [hneg] at h
    exact h.symm

@[expose] def L2ModelFacts : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ Q : Sylow 2 PSL(2, K),
      (∀ β : MulAut PSL(2, K), (∀ z ∈ Subgroup.normalizer ((Q : Subgroup PSL(2, K)) :
          Set PSL(2, K)), Odd (orderOf z) → β z = z) → β = 1) ∧
      ¬ 2 ∣ (oTwoUpper (Subgroup.normalizer ((Q : Subgroup PSL(2, K)) :
          Set PSL(2, K)))).index ∧
      ∀ x : Fin 2 → K, (∀ M : SL(2, K), mk M ∈ oTwoUpper (Subgroup.normalizer
          ((Q : Subgroup PSL(2, K)) : Set PSL(2, K))) →
        (M : Matrix (Fin 2) (Fin 2) K).mulVec x = x) → x = 0

end CFSG.Quasithin
