module

public import CFSG.RankThree.PartTwo.Sec15.F153Main
public import CFSG.RankThree.PartTwo.Sec15.F153ObsR
public import CFSG.RankThree.PartTwo.Sec15.Gagen153Case7
public import CFSG.RankThree.PartTwo.Sec15.F153A10KHolds
public import CFSG.RankThree.PartTwo.Sec15.ThmDFront
public import CFSG.RankThree.PartTwo.Sec15.ThmDA10
public import CFSG.RankThree.PartTwo.Sec15.ThmDL3
public import CFSG.RankThree.PartTwo.Sec15.ThmDK7
public import CFSG.RankThree.PartTwo.Sec15.ThmCMain

public section

namespace CFSG.RankThree.PartTwo.Sec15.F153

open CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.PartTwo.Sec15

section Wiring

theorem step153PushTwinR_of_twinCase7
    (h148 : Item148R) (h149 : Sec16.Item149S14)
    (h152 : Item152R) (h7 : Claim153TwinCase7) : Step153PushTwinR :=
  F153Obs.step153PushTwinR_of_obs (F153Obs.claim153ObsR_of F153Obs.theoremA881
    (claim153TwinTypes_of h148 h149 h152 h7) h149 h152)

theorem claim153CharR_of_frontier_obs
    (h316 : Sec19.Item316) (h149 : Sec16.Item149S14)
    (h148 : Item148R) (h152 : Item152R) (h134 : Item134) (h135 : Item135) (h137 : Item137)
    (h142 : Item142AllS14) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    (hcore : Step153PushCoreR) (h7 : Claim153TwinCase7) (hL3two : Step153PushL3Char2R)
    (hK10 : A10NoV4Offender) : Claim153CharR :=
  claim153CharR_of_frontier h316 h149 h148 h152 h134 h135 h137 h142 h48 h415 hcore
    (step153PushTwinR_of_twinCase7 h148 h149 h152 h7) hL3two hK10

theorem claim153CharR_of_frontier_obs2
    (h316 : Sec19.Item316) (h149 : Sec16.Item149S14)
    (h148 : Item148R) (h152 : Item152R) (h134 : Item134) (h135 : Item135) (h137 : Item137)
    (h142 : Item142AllS14) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    (hcore : Step153PushCoreR) (hL3two : Step153PushL3Char2R) : Claim153CharR :=
  claim153CharR_of_frontier_obs h316 h149 h148 h152 h134 h135 h137 h142 h48 h415 hcore
    (claim153TwinCase7_of_item148R h148) hL3two F153A10K.a10NoV4Offender_holds

theorem claim153CharR_of_frontier_obs3
    (h316 : Sec19.Item316) (h149 : Sec16.Item149S14)
    (h148 : Item148R) (h152 : Item152R) (h134 : Item134) (h135 : Item135) (h137 : Item137)
    (h142 : Item142AllS14) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    (hM2 : ThmC.KFactM2) (h142c : Sec14.Concl142S14) (h143 : Sec14.Concl143S14)
    (h146 : Sec14.Item146S14) (h1444 : Sec14.Item1444S14) (hbot : Sec14.Item145BotS14)
    (hL3 : ThmD.L3FieldFusionK) (hP4 : ThmD.Step148FourKFact)
    (hL3two : Step153PushL3Char2R) : Claim153CharR :=
  claim153CharR_of_frontier_obs2 h316 h149 h148 h152 h134 h135 h137 h142 h48 h415
    (ThmD.step153PushCoreR_of_faithful
        (F153Obs.claim153ObsR_of F153Obs.theoremA881
            (claim153TwinTypes_of h148 h149 h152 (claim153TwinCase7_of_item148R h148)) h149 h152)
        hbot h148 h142c h143 h146
        (ThmC.pCoreOf_mem_scriptQ_of_scriptY0 hM2 h148 h142c h146 h1444 hbot) hP4
        (ThmD.step153D3_of_inputs ThmD.a7CentralizerThreeCycle_holds h142c)
        (ThmD.step153D4_of_inputs hL3 h142c))
    hL3two

end Wiring

end CFSG.RankThree.PartTwo.Sec15.F153
