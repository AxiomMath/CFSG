module

public import CFSG.RankThree.PartTwo.Setup

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree.PartTwo CFSG.Assembly.RankThreeEven

@[expose] def Item4_52Residual : Prop :=
  ∀ (X : Type) [Group X] [Finite X], SectionFourHyp X → Group.IsPerfect X →
    CFSG.pCore 2 X = ⊥ → ∀ (K : Subgroup X) [K.Normal], Group.IsSolvable K →
      ¬ 9 ∣ Nat.card K → Nonempty (X ⧸ K ≃* projSL 3 (GaloisField 2 2)) → IsQuasisimple X

end CFSG.RankThree.PartTwo.Sec4
