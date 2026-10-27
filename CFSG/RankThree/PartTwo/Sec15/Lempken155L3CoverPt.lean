module

public import CFSG.RankThree.PartTwo.Sec15.MathAsch1513Of316

public section

namespace CFSG.RankThree.PartTwo.Sec15.Res1Cover

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec15.Proof15Res6
  CFSG.RankThree.PartTwo.Sec15.Proof1513Steps

variable {G : Type} [Group G] [Finite G]

theorem not_allPointsHJ_of_ctx1514 {A L Y : Subgroup G} {c : G} {LB : Subgroup G → Subgroup G}
    (h : Sec14Std G A c L) (hctx : Ctx1514 A LB c L Y) : ¬ AllPointsHJ A := by
  obtain ⟨p, e, hp, -, hiso, -⟩ := hctx.concl1515
  exact not_allPointsHJ_of_isEmpty h (isEmpty_j2_of_isoLThreePi hiso)


theorem item152_of_ctx1514
    {A L Y : Subgroup G} {c : G} (h : Sec15R G A c L)
    (hctx : Ctx1514 A (lB A) c L Y) : Item152 A (lB A) :=
  Res1Omega1513.item152_nhj Ronan149.item149S14_holds Ronan148M.item148R_holds item134_holds
    Sec11.Close.closed_sec4Item4_8 Sec4.Sporadic.rank3II_4_15 KFacts.kpSz h
    (not_allPointsHJ_of_ctx1514 h.toSec14Std hctx)

theorem claim153Obs_of_ctx1514
    {A L Y : Subgroup G} {c : G} (h : Sec15R G A c L)
    (hctx : Ctx1514 A (lB A) c L Y) : Claim153Obs A (lB A) :=
  Res1PtInputs.claim153Obs_at Ronan148M.item148R_holds Ronan149.item149S14_holds h
    (item152_of_ctx1514 h hctx)

theorem claim153Normal_of_ctx1514
    {A L Y : Subgroup G} {c : G} (h : Sec15R G A c L)
    (hctx : Ctx1514 A (lB A) c L Y) : Claim153Normal A (lB A) :=
  Res1Omega1513.claim153Normal_nhj Ronan148M.item148R_holds Ronan149.item149S14_holds
    item134_holds Sec11.Close.closed_sec4Item4_8 item142AllS14_holds h
    (not_allPointsHJ_of_ctx1514 h.toSec14Std hctx) (item152_of_ctx1514 h hctx)

theorem item153Main_of_ctx1514
    (h316 : Sec19.Item316) {A L Y : Subgroup G} {c : G}
    (h : Sec15R G A c L) (hctx : Ctx1514 A (lB A) c L Y) : Item153Main A (lB A) :=
  Res1PtInputs.item153Main_at h316 Ronan149.item149S14_holds Ronan148M.item148R_holds
    item134_holds item135_holds Ronan137H.item137_holds item142AllS14_holds
    Sec11.Close.closed_sec4Item4_8 Sec4.Sporadic.rank3II_4_15 Ronan148M.concl142S14_holds
    Ronan148M.concl143S14_holds Proof148FourK.item146S14_holds Ronan149.item1444S14_holds
    Ronan149.item145BotS14_holds (item148HJS14_of_wired Ronan148M.item148S14_holds) h
    (item152_of_ctx1514 h hctx)

theorem y4CoreMemAt_of_ctx1514
    {A L Y : Subgroup G} {c : G} (h : Sec15R G A c L)
    (hctx : Ctx1514 A (lB A) c L Y) : Ronan154Big.Y4CoreMemAt A :=
  Ronan154Big.y4CoreMemAt_of_not_allPointsHJ Ronan149.item149S14_holds
    LiebeckClosed.y4CoreMemSolvR_holds item134_holds Sec11.Close.closed_sec4Item4_8 h
    (not_allPointsHJ_of_ctx1514 h.toSec14Std hctx)

end CFSG.RankThree.PartTwo.Sec15.Res1Cover
