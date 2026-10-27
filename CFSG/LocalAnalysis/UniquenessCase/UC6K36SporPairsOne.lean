module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K36SporPairBase
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Assemble
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzThree
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ONPair
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3Three
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2Three
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.HNWitness
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.LyThree
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThThreeClose
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.HNFiveOrders
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.LyFive

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.Spor

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  (sporadicOnePairHolds_J3 sporadicOnePairHolds_McL sporadicOnePairHolds_Suz_three sporadicOnePairHolds_ONan_three
   sporadicOnePairHolds_Co3_three sporadicOnePairHolds_Co2_three sporadicOnePairHolds_HN_three
   sporadicOnePairHolds_Ly_three sporadicOnePairHolds_Th_three sporadicOnePairHolds_HN_five
   sporadicOnePairHolds_Ly_five)

theorem noPlaneAt_J3_three
    (F : SporFacts .J3) : NoPlaneAt .J3 3 :=
  noPlaneAt_of_sporadicOnePairHolds F Nat.prime_three (by norm_num) (sporadicOnePairHolds_J3 F.bridge)

theorem noPlaneAt_McL_three
    (F : SporFacts .McL) : NoPlaneAt .McL 3 :=
  noPlaneAt_of_sporadicOnePairHolds F Nat.prime_three (by norm_num) sporadicOnePairHolds_McL

theorem noPlaneAt_Suz_three
    (F : SporFacts .Suz) : NoPlaneAt .Suz 3 :=
  noPlaneAt_of_sporadicOnePairHolds F Nat.prime_three (by norm_num) sporadicOnePairHolds_Suz_three

theorem noPlaneAt_ONan_three
    (F : SporFacts .ONan) : NoPlaneAt .ONan 3 :=
  noPlaneAt_of_sporadicOnePairHolds F Nat.prime_three (by norm_num) sporadicOnePairHolds_ONan_three

theorem noPlaneAt_Co3_three
    (F : SporFacts .Co3) : NoPlaneAt .Co3 3 :=
  noPlaneAt_of_sporadicOnePairHolds F Nat.prime_three (by norm_num) sporadicOnePairHolds_Co3_three

theorem noPlaneAt_Co2_three
    (F : SporFacts .Co2) : NoPlaneAt .Co2 3 :=
  noPlaneAt_of_sporadicOnePairHolds F Nat.prime_three (by norm_num) sporadicOnePairHolds_Co2_three

theorem noPlaneAt_HN_three
    (F : SporFacts .HN) : NoPlaneAt .HN 3 :=
  noPlaneAt_of_sporadicOnePairHolds F Nat.prime_three (by norm_num) sporadicOnePairHolds_HN_three

theorem noPlaneAt_Ly_three
    (F : SporFacts .Ly) : NoPlaneAt .Ly 3 :=
  noPlaneAt_of_sporadicOnePairHolds F Nat.prime_three (by norm_num) sporadicOnePairHolds_Ly_three

theorem noPlaneAt_Th_three
    (F : SporFacts .Th) : NoPlaneAt .Th 3 :=
  noPlaneAt_of_sporadicOnePairHolds F Nat.prime_three (by norm_num) sporadicOnePairHolds_Th_three

theorem noPlaneAt_HN_five
    (F : SporFacts .HN) : NoPlaneAt .HN 5 :=
  noPlaneAt_of_sporadicOnePairHolds F Nat.prime_five (by norm_num) sporadicOnePairHolds_HN_five

theorem noPlaneAt_Ly_five
    (F : SporFacts .Ly) : NoPlaneAt .Ly 5 :=
  noPlaneAt_of_sporadicOnePairHolds F Nat.prime_five (by norm_num) sporadicOnePairHolds_Ly_five

end CFSG.LocalAnalysis.UniquenessCase.UCK.Spor
