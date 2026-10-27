module

public import CFSG.RankThree.PartTwo.Sec15.Gagen155W315PMain
public import CFSG.RankThree.PartTwo.Sec15.Gagen155W315xQ
import CFSG.RankThree.PartTwo.Sec15.ThmCM2Main

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

namespace Proof155P

theorem step155W315PR_of
    (hSz : KFacts.KPSz)
    (h148 : Item148R) (h142 : Concl142S14) (h143 : Concl143S14)
    (h146 : Item146S14) (h1444 : Item1444S14) (hbot : Item145BotS14)
    (h149 : Sec16.Item149S14) (hY4 : Y4CoreMemR) : Step155W315PR := by
  intro G _ _ A c L hR
  exact step155W315P_of hSz (h142 G A c L hR.toSec14Std) (h143 G A c L hR.toSec14Std)
    (h146 G A c L hR.toSec14Std) (h148 G A c L hR) (h149 G A c L hR.toSec14Std)
    (ThmC.pCoreOf_mem_scriptQ_of_scriptY0_free h148 h142 h146 h1444 hbot G A c L hR)
    (hY4 G A c L hR)

theorem step155W315xR_of_inputs
    (hst : StellmacherKP) (hSz : KFacts.KPSz) (h148 : Item148R)
    (h142 : Concl142S14) (h143 : Concl143S14) (h146 : Item146S14) (h1444 : Item1444S14)
    (hbot : Item145BotS14) (h149 : Sec16.Item149S14) (hY4 : Y4CoreMemR) :
    Step155W315xR :=
  step155W315xR_of_P hst h146 h1444 h148 h149
    (step155W315PR_of hSz h148 h142 h143 h146 h1444 hbot h149 hY4)

end Proof155P

end CFSG.RankThree.PartTwo.Sec15
