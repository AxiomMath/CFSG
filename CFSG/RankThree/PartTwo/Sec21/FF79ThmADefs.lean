module

public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

@[expose] def FF79KNoInvA5 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (n : ℕ), (n = 4 ∨ n = 5) →
    StatedClassicalModel Y .PSL n 2 1 → ∀ K : Subgroup Y, StatedClassicalModel K .PSL 2 2 2 →
      ∀ t : Y, orderOf t = 2 → ¬ K ≤ Cen t

@[expose] def FF79KL34a : Prop :=
  ∀ (E : Type) [Group E] [Finite E], StatedClassicalModel E .PSL 3 2 2 →
    ∀ β : MulAut E, β ^ 3 = 1 → ∀ S : Subgroup E, Nat.card S = 9 → (∀ s ∈ S, β s ∈ S) →
      (∃ K : Subgroup E, StatedClassicalModel K .PSL 2 2 2 ∧ ∀ x ∈ K, β x = x) →
      ∃ q : E, (∀ s ∈ S, q * s * q⁻¹ ∈ S) ∧ β (q ^ 2) = q ^ 2 ∧ q ^ 2 ≠ 1 ∧ q ^ 4 = 1

@[expose] def FF79KL34b : Prop :=
  ∀ (E : Type) [Group E] [Finite E], StatedClassicalModel E .PSL 3 2 2 →
    ∀ S : Subgroup E, Nat.card S = 9 → ∀ φ : MulAut E, (∀ s ∈ S, φ s = s) → φ ^ 4 = 1 →
      φ ^ 2 = 1

@[expose] def FF79KL34 : Prop := FF79KL34a ∧ FF79KL34b

end CFSG.RankThree.PartTwo.Sec21.FF79
