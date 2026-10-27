module

public import CFSG.RankThree.PartTwo.Sec14.Item148Steps
public import CFSG.RankThree.PartTwo.Sec15.Item156ProofType
import CFSG.RankThree.PartTwo.Sec13.Item13Basic

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem item148Small_of_item148
    {A : Subgroup G} {LB : Subgroup G → Subgroup G} (hAab : IsMulCommutative A)
    (hch : Chosen136 A) (h148 : Item148 A LB) : Item148Small A LB :=
  fun _ hY hq hcard => Sec15.exists_hj_of_img148 h148 hY hAab hch hq hcard

theorem item148SmallS14_of_item148S14
    (h148 : Item148S14) : Item148SmallS14 :=
  fun G _ _ A c L h =>
    item148Small_of_item148 h.isElemAbelian.1 h.chosen136 (h148 G A c L h)

end CFSG.RankThree.PartTwo.Sec14
