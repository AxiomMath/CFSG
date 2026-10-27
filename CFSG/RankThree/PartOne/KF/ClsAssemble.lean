module

public import CFSG.RankThree.PartOne.KF.Rows123
public import CFSG.RankThree.PartOne.KF.ClsPSL
public import CFSG.RankThree.PartOne.KF.ClsPSp
public import CFSG.RankThree.PartOne.KF.ClsPSU
public import CFSG.RankThree.PartOne.KF.ClsPOmegaPlus
public import CFSG.RankThree.PartOne.KF.ClsOmegaMinusQPlus
public import CFSG.RankThree.PartOne.KF.ClsExcE6
public import CFSG.RankThree.PartOne.KF.ClsExcF4Two
public import CFSG.RankThree.PartOne.KF.ClsExcD4
public import CFSG.RankThree.PartOne.KF.ClsExcG2
public import CFSG.RankThree.PartOne.KF.ClsSz
public import CFSG.RankThree.PartOne.KF.ClsTits

public section

namespace CFSG.RankThree.PartOne

theorem kf123Classify_of_inputs
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSpin : Census3.SpinRankFour) (hExc : Census3.ExceptionalRankFour)
    (hTwF4 : KF123ExcTwF4NoRankTwo) : KF123Classify := by
  refine kf123Classify_of_tags fun t => ?_
  cases t with
  | PSL => exact kf123ClassifyTag_PSL hGA
  | PSU => exact kf123ClassifyTag_PSU hGA
  | PSp => exact kf123ClassifyTag_PSp hGA
  | POmegaOdd => exact kf123ClassifyTag_POmegaOdd
  | POmegaPlus => exact kf123ClassifyTag_POmegaPlus hGA hSpin
  | POmegaMinus => exact kf123ClassifyTag_POmegaMinus hGA hSpin omegaEightMinusNotTwo
  | G2 => exact kf123ClassifyTag_G2 kf123ExcG2NoRankTwo
  | F4 => exact kf123ClassifyTag_F4 hGA hExc kf123ExcF4TwoNoRankTwo
  | E6 => exact kf123ClassifyTag_E6 hGA hExc
  | E7 => exact kf123ClassifyTag_E7 hGA hExc
  | E8 => exact kf123ClassifyTag_E8 hGA hExc
  | twistedE6 => exact kf123ClassifyTag_twistedE6 hGA hExc
  | trialityD4 => exact kf123ClassifyTag_trialityD4 kf123ExcD4NoRankTwo
  | twistedB2 => exact kf123ClassifyTag_twistedB2
  | twistedG2 => exact kf123ClassifyTag_twistedG2
  | twistedF4 => exact kf123ClassifyTag_twistedF4 hTwF4
  | Tits => exact kf123ClassifyTag_Tits

theorem kf123_of_inputs
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSpin : Census3.SpinRankFour) (hExc : Census3.ExceptionalRankFour)
    (hTwF4 : KF123ExcTwF4NoRankTwo) : KF123 :=
  kf123_of_classify hGA
    (kf123Classify_of_inputs hGA hSpin hExc hTwF4)

theorem kf123NoTransvection_of_inputs
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSpin : Census3.SpinRankFour) (hExc : Census3.ExceptionalRankFour)
    (hTwF4 : KF123ExcTwF4NoRankTwo) : KF123NoTransvection :=
  kf123NoTransvection_of_classify hGA
    (kf123Classify_of_inputs hGA hSpin hExc hTwF4)

end CFSG.RankThree.PartOne
