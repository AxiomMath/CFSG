module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.RankThree.PartTwo.Sec4.Item413Inputs

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def Inputs413CoverON : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L A E : Subgroup G) (c : G), Hyp413 L A E c →
    IsExtOf (L ⧸ aschbacherSolvableCore 3 L) Blueprint.NativeSporadic.ON
      (Multiplicative (ZMod 3)) → False

end CFSG.RankThree.PartTwo.Sec4
