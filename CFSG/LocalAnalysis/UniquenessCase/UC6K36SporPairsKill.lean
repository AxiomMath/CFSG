module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K36SporPairBase
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.Three
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.HeFive
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.RuFive
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.Co2Five
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.Co3Five
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.HSFive
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.McLFive
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.ThFivePair
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.HeSeven
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.ThSevenPair
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.ON7Model
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.J4ElevenPair
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.SuzFiveGen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.Spor

open CFSG.HardMathSupport.Timmesfeld.Coordinator (SporadicOuterLeTwo)
open CFSG.Sporadic.SuzOddCore (suzEquivM)

theorem noPlaneAt_M11_three
    (hOut : SporadicOuterLeTwo)
    (F : SporFacts .M11) : NoPlaneAt .M11 3 :=
  noPlaneAt_of_sporPlaneKill F Nat.prime_three (by norm_num)
    (CFSG.HardMathSupport.Dickson.I271.sporPlaneKill_M11_three hOut)

theorem noPlaneAt_M23_three
    (hOut : SporadicOuterLeTwo)
    (F : SporFacts .M23) : NoPlaneAt .M23 3 :=
  noPlaneAt_of_sporPlaneKill F Nat.prime_three (by norm_num)
    (CFSG.HardMathSupport.Dickson.I271.sporPlaneKill_M23_three hOut)

theorem noPlaneAt_M24_three
    (hOut : SporadicOuterLeTwo) (F : SporFacts .M24) : NoPlaneAt .M24 3 :=
  noPlaneAt_of_sporPlaneKill F Nat.prime_three (by norm_num)
    (CFSG.HardMathSupport.Dickson.I271.sporPlaneKill_M24_three hOut)

theorem noPlaneAt_HS_three
    (hOut : SporadicOuterLeTwo) (F : SporFacts .HS) : NoPlaneAt .HS 3 :=
  noPlaneAt_of_sporPlaneKill F Nat.prime_three (by norm_num)
    (CFSG.HardMathSupport.Dickson.I271.sporPlaneKill_HS_three hOut)

theorem noPlaneAt_He_three
    (hOut : SporadicOuterLeTwo)
    (F : SporFacts .He) : NoPlaneAt .He 3 :=
  noPlaneAt_of_sporPlaneKill F Nat.prime_three (by norm_num)
    (CFSG.HardMathSupport.Dickson.I271.sporPlaneKill_He_three hOut)

theorem noPlaneAt_Ru_three
    (hOut : SporadicOuterLeTwo)
    (F : SporFacts .Ru) : NoPlaneAt .Ru 3 :=
  noPlaneAt_of_sporPlaneKill F Nat.prime_three (by norm_num)
    (CFSG.HardMathSupport.Dickson.I271.sporPlaneKill_Ru_three hOut)

theorem noPlaneAt_J4_three
    (hOut : SporadicOuterLeTwo) (F : SporFacts .J4) : NoPlaneAt .J4 3 :=
  noPlaneAt_of_sporPlaneKill F Nat.prime_three (by norm_num)
    (CFSG.HardMathSupport.Dickson.I271.sporPlaneKill_J4_three hOut)

theorem noPlaneAt_He_five
    (hOut : SporadicOuterLeTwo)
    (F : SporFacts .He) : NoPlaneAt .He 5 :=
  noPlaneAt_of_sporPlaneKill F Nat.prime_five (by norm_num)
    (CFSG.HardMathSupport.Dickson.I271.sporPlaneKill_He_five hOut)

theorem noPlaneAt_Ru_five
    (hOut : SporadicOuterLeTwo)
    (F : SporFacts .Ru) : NoPlaneAt .Ru 5 :=
  noPlaneAt_of_sporPlaneKill F Nat.prime_five (by norm_num)
    (CFSG.HardMathSupport.Dickson.I271.sporPlaneKill_Ru_five hOut)

theorem noPlaneAt_Co2_five
    (hOut : SporadicOuterLeTwo) (F : SporFacts .Co2) : NoPlaneAt .Co2 5 :=
  noPlaneAt_of_sporPlaneKill F Nat.prime_five (by norm_num)
    (CFSG.HardMathSupport.Dickson.I271.sporPlaneKill_Co2_five hOut)

theorem noPlaneAt_Co3_five
    (hOut : SporadicOuterLeTwo) (F : SporFacts .Co3) : NoPlaneAt .Co3 5 :=
  noPlaneAt_of_sporPlaneKill F Nat.prime_five (by norm_num)
    (CFSG.HardMathSupport.Dickson.I271.sporPlaneKill_Co3_five hOut)

theorem noPlaneAt_HS_five
    (hOut : SporadicOuterLeTwo)
    (F : SporFacts .HS) : NoPlaneAt .HS 5 :=
  noPlaneAt_of_sporPlaneKill F Nat.prime_five (by norm_num)
    (CFSG.HardMathSupport.Dickson.I271.sporPlaneKill_HS_five hOut)

theorem noPlaneAt_McL_five
    (hOut : SporadicOuterLeTwo) (F : SporFacts .McL) : NoPlaneAt .McL 5 :=
  noPlaneAt_of_sporPlaneKill F Nat.prime_five (by norm_num)
    (CFSG.HardMathSupport.Dickson.I271.sporPlaneKill_McL_five hOut)

theorem noPlaneAt_Th_five
    (hOut : SporadicOuterLeTwo) (F : SporFacts .Th) : NoPlaneAt .Th 5 :=
  noPlaneAt_of_sporPlaneKill F Nat.prime_five (by norm_num)
    (CFSG.HardMathSupport.Dickson.I271.sporPlaneKill_Th_five hOut)

theorem noPlaneAt_He_seven
    (hOut : SporadicOuterLeTwo) (F : SporFacts .He) : NoPlaneAt .He 7 :=
  noPlaneAt_of_sporPlaneKill F (by norm_num) (by norm_num)
    (CFSG.HardMathSupport.Dickson.I271.sporPlaneKill_He_seven hOut)

theorem noPlaneAt_Th_seven
    (hOut : SporadicOuterLeTwo) (F : SporFacts .Th) : NoPlaneAt .Th 7 :=
  noPlaneAt_of_sporPlaneKill F (by norm_num) (by norm_num)
    (CFSG.HardMathSupport.Dickson.I271.sporPlaneKill_Th_seven hOut)

theorem noPlaneAt_ONan_seven
    (hOut : SporadicOuterLeTwo)
    (F : SporFacts .ONan) : NoPlaneAt .ONan 7 :=
  noPlaneAt_of_sporPlaneKill F (by norm_num) (by norm_num)
    (CFSG.HardMathSupport.Dickson.I271.sporPlaneKill_ONan_seven hOut)

theorem noPlaneAt_J4_eleven
    (hOut : SporadicOuterLeTwo) (F : SporFacts .J4) : NoPlaneAt .J4 11 :=
  noPlaneAt_of_sporPlaneKill F (by norm_num) (by norm_num)
    (CFSG.HardMathSupport.Dickson.I271.sporPlaneKill_J4_eleven hOut)

theorem noPlaneAt_Suz_five
    (F : SporFacts .Suz) : NoPlaneAt .Suz 5 :=
  noPlaneAt_of_centGen F Nat.prime_five (by norm_num)
    (CFSG.HardMathSupport.Dickson.I271.CentGen.of_mulEquiv (suzEquivM.symm.trans F.bridge.some)
      CFSG.HardMathSupport.Dickson.I271.centGen_suzM_five)

end CFSG.LocalAnalysis.UniquenessCase.UCK.Spor
