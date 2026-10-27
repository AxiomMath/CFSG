module

public import CFSG.RankThree.PartTwo.Sec15.ThmCM2Mult
public import CFSG.RankThree.PartTwo.Sec15.F153MainObs
public import CFSG.RankThree.PartTwo.Sec15.F153L3KCent
public import CFSG.RankThree.PartTwo.Sec15.F153L3KFus
public import CFSG.RankThree.PartTwo.Sec15.F153L3KOut
public import CFSG.RankThree.PartTwo.Sec15.ThmDK148Front
public import CFSG.RankThree.PartTwo.Sec15.ThmDK148Chain
public import CFSG.RankThree.PartTwo.Sec14.Ronan148MAssembly3
public import CFSG.RankThree.PartTwo.Sec15.F153L3C2Main

public section

namespace CFSG.RankThree.PartTwo.Sec15.F153

open CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.PartTwo.Sec15

section Wiring

theorem claim153CharR_of_frontier_obs8
    (h316 : Sec19.Item316) (h149 : Sec16.Item149S14)
    (h148 : Item148R) (h152 : Item152R) (h134 : Item134) (h135 : Item135) (h137 : Item137)
    (h142 : Item142AllS14) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    (h142c : Sec14.Concl142S14) (h143 : Sec14.Concl143S14)
    (h146 : Sec14.Item146S14) (h1444 : Sec14.Item1444S14) (hbot : Sec14.Item145BotS14)
    (h148HJ : Sec14.Item148HJS14) : Claim153CharR :=
  claim153CharR_of_frontier_obs2 h316 h149 h148 h152 h134 h135 h137 h142 h48 h415
    (ThmD.step153PushCoreR_of_inputs_v2 ThmC.kFactM2_of_certificates h148 h149 h152 h142c h143
      h146 h1444 hbot F153L3K.l3FieldFusionK_holds (ThmD.step148FourKFact'_of_steps
          (step148YB_of_shape step148YBShape_holds) Ronan148M.step148HJ_holds
          Ronan148C.step148Core_holds Ronan148M.step148Point_holds Ronan148M.step148KType_holds
          Ronan148M.step148Lift_holds Ronan148M.step148D4_holds h148 h134 h48))
    (F153L3C2.step153PushL3Char2R_of_inputs h134 h48 h149 (claim153TwinR_of_items h148 h149 h152)
      h148HJ F153L3K.kFactL3NoOuterOffender_holds F153L3K.kFactL3CentOdd_holds)

end Wiring

end CFSG.RankThree.PartTwo.Sec15.F153
