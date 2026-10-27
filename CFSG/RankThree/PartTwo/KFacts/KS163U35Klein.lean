module

public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.Assembly.RankThreeEven (projSU)

@[expose] def KS163U35InvTwo : Prop :=
  ∀ (_ : Fact (Nat.Prime 5)) (E : Subgroup ↥(projSU 3 5 1)), Nat.card E = 9 →
    ∀ V : Subgroup ↥(projSU 3 5 1), IsPGroup 2 V →
      E ≤ Subgroup.normalizer (V : Set ↥(projSU 3 5 1)) → V ≠ ⊥ →
        Nat.card V = 4 ∧ ∀ W : Subgroup ↥(projSU 3 5 1), W ≤ V →
          E ≤ Subgroup.normalizer (W : Set ↥(projSU 3 5 1)) → W = ⊥ ∨ W = V

@[expose] def KS163U35KleinGen : Prop :=
  ∀ (_ : Fact (Nat.Prime 5)) (E : Subgroup ↥(projSU 3 5 1)), Nat.card E = 9 →
    ∀ V₁ V₂ : Subgroup ↥(projSU 3 5 1), IsPGroup 2 V₁ → IsPGroup 2 V₂ →
      E ≤ Subgroup.normalizer (V₁ : Set ↥(projSU 3 5 1)) →
      E ≤ Subgroup.normalizer (V₂ : Set ↥(projSU 3 5 1)) → V₁ ≠ ⊥ → V₂ ≠ ⊥ → V₁ ≠ V₂ →
        Nonempty (↥(V₁ ⊔ V₂) ≃* alternatingGroup (Fin 7))

end CFSG.RankThree.PartTwo.KFacts
