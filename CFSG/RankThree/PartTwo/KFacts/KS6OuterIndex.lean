module

public import CFSG.RankThree.PartTwo.Sec4.Notation

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

@[expose] def KS6OuterIndex : Prop :=
  ∀ (X : Type) [Group X] [Finite X], SectionFourHyp X → 3 ∣ Nat.card (Subgroup.center X) →
    ∀ L ∈ thetaComponents 3 X, ∀ F : Subgroup X, CFSG.Assembly.IsElemAbelian 3 F →
      F ≤ Subgroup.normalizer (L : Set X) →
      Nat.card F ≤ 3 * Nat.card (F ⊓ (L ⊔ thetaQuotCentralizer L) : Subgroup X)

end CFSG.RankThree.PartTwo.KFacts
