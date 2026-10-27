module

public import CFSG.RankThree.PartTwo.Sec14.Concl142HJ
public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements

public section

namespace CFSG.RankThree.PartTwo.Sec14


@[expose] def Item148HJS14 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → AllPointsHJ A → Item148 A (lB A)

@[expose] def Item148NHJS14 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ¬ AllPointsHJ A → Item148 A (lB A)

end CFSG.RankThree.PartTwo.Sec14
