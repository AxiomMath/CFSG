module

public import CFSG.RankThree.PartTwo.Sec17.Item17Statements

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15

@[expose] def Item1730HJ : Prop :=
  ∀ (G : Type) [Group G] [Finite G], PartTwoStanding G → partTwoS G = ∅ →
    ∀ A ∈ partTwoE G, A ∉ partTwoT G → ∀ c : G, Subgroup.zpowers c ∈ omegaA A →
      ∀ L ∈ lA A c, IsEmpty (↥L ⧸ CFSG.pCore 2 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)

theorem item1730HJ_of_item1730 (h : Item1730) : Item1730HJ :=
  fun G _ _ hst hS A hA hAT c hc L hL => (h G hst hS A hA hAT c hc L hL).2

end CFSG.RankThree.PartTwo.Sec17
