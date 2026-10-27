module

public import CFSG.RankThree.PartTwo.Sec15.Item153PushProof

public section

namespace CFSG.RankThree.PartTwo.Sec15

theorem claim153CharR_of_types (h315 : Item3_15) (h316 : Sec19.Item316)
    (h149 : Sec16.Item149S14) (htwin : Claim153TwinR) (hcore : Step153PushCoreR)
    (htw : Step153PushTwinR) (hlist : Step153PushListedR) (hHJ : Step153PushHJR)
    (hL3 : Step153PushL3R) (hM22 : Step153PushM22R) (hM12 : Step153PushM12R)
    (hA10 : Step153PushA10R) (hrest : Step153PushRestR) : Claim153CharR :=
  claim153CharR_of_twin h315 h316 h149 htwin
    (step153CharPush_of_types h149 htwin hcore htw hlist hHJ hL3 hM22 hM12 hA10 hrest)

end CFSG.RankThree.PartTwo.Sec15
