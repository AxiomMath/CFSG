module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20g

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

@[expose] def KLeviRank208 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsQuasisimple X → Odd (Nat.card (center X)) →
    UC22P20gShape X → ∀ P : Subgroup X, IsParabolicTwo X P → P ≠ ⊤ →
      ∀ n : ℕ, 2 < n →
        (IsL2 (Bar2 (Hinf P)) n ∨ IsSz (Bar2 (Hinf P)) n ∨ IsSzL2Product (Bar2 (Hinf P)) n) →
        ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ 2 ^ n - 1 ∧
          CFSG.Open.pRank p (Hinf P) < CFSG.Open.pRank p (⊤ : Subgroup X)

end CFSG.LocalAnalysis.UniquenessCase.UC22
