module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.AltLocal17

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)

@[expose] def K_L33GraphOuterW : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K S : Subgroup Y), KYForm Y K S →
    LieModel ↥K .PSL 3 3 1 → ¬ S ≤ K →
    ∃ X : Subgroup Y, X ≤ K ∧ Nat.card X = 3 ∧ Permutes X S ∧
      ∀ R A : Subgroup Y, R ≤ S → X ⊔ S ≤ Subgroup.normalizer (R : Set Y) → A ≤ R →
        IsElemAbelian 2 A → ¬ A ≤ K →
          ∃ x ∈ X, ∃ Z S' : Subgroup Y, Nat.card Z = 3 ∧ S' ≤ S ∧ Permutes Z S' ∧
            CFSG.Quasithin.conjSubgroup A x ≤ S' ∧
            ∀ R' : Subgroup Y, CFSG.Quasithin.conjSubgroup A x ≤ R' → R' ≤ S' →
              ¬ Z ⊔ (S ⊓ Subgroup.normalizer (S' : Set Y)) ≤ Subgroup.normalizer (R' : Set Y)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
