module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102KFacts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open

@[expose] def KU45KeyDvd : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), IsU45 X n →
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → p ∣ 2 ^ n + 1 →
      ∀ R : Subgroup (MulAut X), IsElemAbelian p R →
        ∃ S : Subgroup X, IsPGroup 3 S ∧ ¬ 3 ∣ S.index ∧
          ∃ C : Subgroup (MulAut X), C ≤ R ∧ (∀ α ∈ C, ∀ s ∈ S, α s = s) ∧
            Nat.card R ≤ p ^ 2 * Nat.card C

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

end
