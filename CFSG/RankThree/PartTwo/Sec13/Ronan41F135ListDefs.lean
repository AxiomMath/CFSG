module

public import CFSG.RankThree.PartTwo.Sec4.Census.Interface

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

@[expose] def ComponentList42 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] (M : Subgroup G), SectionFourHyp M →
    ∀ (R : Subgroup M) [R.Normal] (J : Subgroup (M ⧸ R)), CFSG.IsComponent J →
      Sec4.Census.List42 (J ⧸ Subgroup.center J)

end CFSG.RankThree.PartTwo.Sec13.F135Last
