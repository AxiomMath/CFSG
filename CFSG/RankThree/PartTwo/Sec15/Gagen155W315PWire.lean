module

public import CFSG.RankThree.PartTwo.Sec15.Gagen155W315xRoute
public import CFSG.RankThree.PartTwo.Sec15.Gagen155W315PRoute
import CFSG.RankThree.PartTwo.Sec15.Sylow155KSL3
import CFSG.RankThree.PartTwo.KFacts.KS44Sz
import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KS155.J2E4

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14

theorem item155wR_of_corr9Cert
    (h152 : Item152R) (h153 : Item153MainR) (h154 : Item154PiR)
    (h315 : Item3_15) (h316 : Sec19.Item316) (h1444 : Item1444S14)
    (h146 : Item146S14) (hbot : Item145BotS14) (h149 : Sec16.Item149S14)
    (h142 : Concl142S14) (h148 : Item148R) (h134 : Item134) (h48 : Sec4.Item4_8)
    (hUp : Step155UpPiNHJR) (halt : Step155GrowAltTwoFieldWR) (hYQ : Step155YQ0HypWR)
    (hPJQ : Step155PJQ0HypWR) (htwo : Step155CasesTwoNHJWR)
    (hst : StellmacherKP) (h143 : Concl143S14)
    (hY4 : Y4CoreMemR) (hfr : Step155FrattiniNWPR) : Item155wR :=
  item155wR_of_corr8Cert h152 h153 h154 h315 h316 h1444 h146 hbot h149 h142 h148 h134 h48
    CFSG.AGLEmbeddingD2.Wilson.Coordinator.KS155.ks155J2CentE4 kSL3NonPiAutThree hUp halt hYQ
    hPJQ htwo
    (Proof155P.step155W315xR_of_inputs hst KFacts.kpSz h148 h142 h143 h146 h1444 hbot h149
      hY4) hfr

theorem item156R_of_steps155w9Cert
    (h148 : Item148R) (h152 : Item152R) (h149 : Sec16.Item149S14) (h315 : Item3_15)
    (h316 : Sec19.Item316) (h1411 : Item1411_1R) (h134 : Item134)
    (h48 : Sec4.Item4_8) (h142 : Item142AllS14) (h154 : Item154PiR) (h1444 : Item1444S14)
    (h146 : Item146S14) (hbot : Item145BotS14) (hpush : Step153CharPush)
    (hrest : Step156CQA5DFaithR) (hc142 : Concl142S14) (hUp : Step155UpPiNHJR)
    (halt : Step155GrowAltTwoFieldWR) (hYQ : Step155YQ0HypWR) (hPJQ : Step155PJQ0HypWR)
    (htwo : Step155CasesTwoNHJWR) (hst : StellmacherKP)
    (h143 : Concl143S14) (hY4 : Y4CoreMemR)
    (hfr : Step155FrattiniNWPR) : Item156R :=
  item156R_of_steps155w8Cert h148 h152 h149 h315 h316 h1411 h134 h48 h142 h154 h1444 h146
    hbot hpush hrest hc142
    CFSG.AGLEmbeddingD2.Wilson.Coordinator.KS155.ks155J2CentE4 kSL3NonPiAutThree hUp halt hYQ
    hPJQ htwo
    (Proof155P.step155W315xR_of_inputs hst KFacts.kpSz h148 hc142 h143 h146 h1444 hbot h149
      hY4) hfr

theorem item155R_of_steps155w9Cert
    (h148 : Item148R) (h152 : Item152R) (h149 : Sec16.Item149S14) (h315 : Item3_15)
    (h316 : Sec19.Item316) (h1411 : Item1411_1R) (h134 : Item134)
    (h48 : Sec4.Item4_8) (h142 : Item142AllS14) (h154 : Item154PiR) (h1444 : Item1444S14)
    (h146 : Item146S14) (hbot : Item145BotS14) (hpush : Step153CharPush)
    (hrest : Step156CQA5DFaithR) (hc142 : Concl142S14) (hUp : Step155UpPiNHJR)
    (halt : Step155GrowAltTwoFieldWR) (hYQ : Step155YQ0HypWR) (hPJQ : Step155PJQ0HypWR)
    (htwo : Step155CasesTwoNHJWR) (hst : StellmacherKP)
    (h143 : Concl143S14) (hY4 : Y4CoreMemR)
    (hfr : Step155FrattiniNWPR) : Item155R :=
  item155R_of_steps155w8Cert h148 h152 h149 h315 h316 h1411 h134 h48 h142 h154 h1444 h146
    hbot hpush hrest hc142
    CFSG.AGLEmbeddingD2.Wilson.Coordinator.KS155.ks155J2CentE4 kSL3NonPiAutThree hUp halt hYQ
    hPJQ htwo
    (Proof155P.step155W315xR_of_inputs hst KFacts.kpSz h148 hc142 h143 h146 h1444 hbot h149
      hY4) hfr

end CFSG.RankThree.PartTwo.Sec15
