module

public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bPlan

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def YCfgMixed : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E F : Subgroup G) (a b : G)
    (R Y : Subgroup G), YCfg G A c L E F a b R Y →
      b ∉ E ⊓ Sec4.thetaQuotCentralizer L ∧ b ∉ E ⊓ L

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b
