module

public import CFSG.RankThree.PartTwo.Sec15.Lempken155L3CoverPt
public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1L3Even1520Core

public section

namespace CFSG.RankThree.PartTwo.Sec15.Y4Core

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Sec19
  CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.LocalRank CFSG.GH74.GLS

open scoped Pointwise


variable {G : Type} [Group G] [Finite G]

theorem step1520CoreComp_holds
    : Step1520CoreComp :=
  Res1Cover.step1520CoreComp_of_at
    (Read148Perf.y4CoreReadR_from_item148R KFacts.kpSz Ronan149.item145BotS14_holds
      Ronan148M.item148R_holds)
    Ronan149.item145BotS14_holds
    (fun G _ _ A c L h Y hctx => Res1Cover.y4CoreMemAt_of_ctx1514 h hctx)

end CFSG.RankThree.PartTwo.Sec15.Y4Core
