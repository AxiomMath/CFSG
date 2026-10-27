module

public import CFSG.RankThree.PartTwo.Sec4.StatementsComponents

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.RankThree.LocalRank (aschbacherSolvableCore)

@[expose] def KFOut3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G), Group.IsPerfect K →
    CFSG.IsQuasisimple (K ⧸ aschbacherSolvableCore 3 K) →
    Sec4.IsList46 (K ⧸ aschbacherSolvableCore 3 K) →
    ∀ β ∈ Subgroup.normalizer (K : Set G), IsPGroup 3 (Subgroup.zpowers β) →
    ∀ R : Subgroup G, IsPGroup 2 R → R ≤ Subgroup.normalizer (K : Set G) →
      β ∈ Subgroup.normalizer (R : Set G) → ⁅R, Subgroup.zpowers β⁆ = R →
        R ≤ K ⊔ Sec4.thetaQuotCentralizer K

end CFSG.RankThree.PartTwo.KFacts
