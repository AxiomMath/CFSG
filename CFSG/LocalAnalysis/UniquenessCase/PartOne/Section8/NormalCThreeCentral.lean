module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

theorem normal_card_three_le_center_of_isPGroup_three
    {G : Type} [Group G] [Finite G] (hG : IsPGroup 3 G) {N : Subgroup G}
    (hN : N.Normal) (hcard : Nat.card N = 3) :
    N ≤ Subgroup.center G := by
  haveI : Fact (IsPGroup 3 G) := ⟨hG⟩
  haveI : N.Normal := hN
  exact normal_subgroup_card_eq_prime_le_center (p := 3) N hcard

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
