module

public import CFSG.RankThree.PartTwo.Sec15.F153HJ
public import CFSG.RankThree.PartTwo.Sec15.F153M22
public import CFSG.RankThree.PartTwo.Sec15.F153U33
public import CFSG.RankThree.PartTwo.Sec15.F153A10
public import CFSG.RankThree.PartTwo.Sec15.Item1523Res3ProofLink
public import CFSG.RankThree.PartTwo.Sec15.Item153PushProofM12
public import CFSG.RankThree.PartTwo.Sec15.Item153Twin3Proof
public import CFSG.RankThree.PartTwo.Sec15.Item153PushProofMain
public import CFSG.RankThree.PartTwo.Sec15.SimsBaumannMain

public section

namespace CFSG.RankThree.PartTwo.Sec15.F153

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS
open CFSG.HardMathSupport.Cooperstein.Coordinator

section Wiring




theorem claim153CharR_of_frontier
    (h316 : Sec19.Item316) (h149 : Sec16.Item149S14)
    (h148 : Item148R) (h152 : Item152R) (h134 : Item134) (h135 : Item135) (h137 : Item137)
    (h142 : Item142AllS14) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    (hcore : Step153PushCoreR) (htw : Step153PushTwinR) (hL3two : Step153PushL3Char2R)
    (hK10 : A10NoV4Offender) : Claim153CharR := by
  have htwin : Claim153TwinR := claim153TwinR_of_items h148 h149 h152
  exact claim153CharR_of_types item3_15_holds h316 h149 htwin hcore htw
    (step153PushListedR_of_item148R h148 h134 h48) (step153PushHJR_of_inputs h149 htwin)
    (step153PushL3R_of_inputs h149 htwin hL3two (step153PushU33R_of_inputs h148 h134 h48))
    (step153PushM22R_of_inputs h149 htwin)
    (step153PushM12R_of_item157 h137 h142 h134 h135 h48 h415 h148)
    (step153PushA10R_of_inputs hK10 h149 htwin)
    (step153PushRestR_of_inputs h148 h134 h48 h149 htwin)

end Wiring

end CFSG.RankThree.PartTwo.Sec15.F153
