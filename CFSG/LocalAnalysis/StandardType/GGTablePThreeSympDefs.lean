module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeKnownSix
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSplitR
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly

@[expose] def SympShapeConcl {X : Type} [Group X] (n : ℕ) (A : Subgroup (MulAut X))
    (J : Subgroup X) : Prop :=
  (∃ a : ℕ, 2 ≤ a ∧ 3 ∣ 2 ^ n - 1 ∧ GGHasLabel ⟨.A, a - 1, n⟩ (↥J ⧸ Subgroup.center ↥J) ∧
      (a = 3 → Subgroup.center J ≠ ⊥) ∧ (a = 2 → Nat.card A < 3 ^ 3)) ∨
    (n = 1 ∧ ∃ a : ℕ, 4 ≤ a ∧ GGHasLabel ⟨.twA, a - 1, 1⟩ (↥J ⧸ Subgroup.center ↥J)) ∨
    (∃ s : ℕ, 2 ≤ s ∧ ¬ (s = 2 ∧ n = 1) ∧ GGHasLabel ⟨.C, s, n⟩ (↥J ⧸ Subgroup.center ↥J)) ∨
    (n = 1 ∧ Nat.card (↥J ⧸ Subgroup.center ↥J) = 360)

end CFSG.StandardType.TablePThreeKG

end
