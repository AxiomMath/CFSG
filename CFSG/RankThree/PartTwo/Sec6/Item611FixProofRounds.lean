module

public import CFSG.RankThree.PartTwo.Sec6.Item611FixProofWire

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

section CertsMain

theorem item6_11_1_of_res6Fix (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h49 : Sec4.Item4_9)
    (hKf : KFacts.KS6OuterIndex) (h41 : Sec4.Item4_1LargePrime)
    (h413 : Sec4.Item4_13_forwardFix) (h641 : Item6_4_1) (hM : Item611FieldL2Max)
    (hV : Item611E81V) (hCore : Item611E81Core) : Item6_11_1 :=
  item6_11_1_of_res5Fix h45 h48 h49 hKf h41 h413 h641 kCentCharThreeU43_holds hM hV hCore

end CertsMain

end CFSG.RankThree.PartTwo.Sec6
