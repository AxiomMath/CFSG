module

public import CFSG.RankThree.PartTwo.Sec12.Hering129KD1
public import CFSG.RankThree.PartTwo.Sec12.Hering129KR3
public import CFSG.RankThree.PartTwo.Sec12.Hering129KM6
public import CFSG.RankThree.PartTwo.Sec12.Hering129LFix

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem item129Bar_of_inputs_R3
    (h1 : Sec4.Item4_1LargePrime) (h2 : Sec4.Item4_1ThreeCover) (h43 : Sec4.Item4_3)
    (hcov : Sec4.Census.CoverInputs46)
    (hKC : KFacts.KS12CoverExclusion) (h128 : Item128BarAt) (hNF : KS128NotHJFree)
    (h422 : Sec4.Item4_22) (h423 : Sec4.Item4_23) (h424 : Sec4.Item4_24Used)
    (hN : Sec11.Item1134E27N) (hST : Sec21.Item1134E27ST)
    (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h49 : Sec4.Item4_9)
    (hB3 : Sec6.BThreePropertyCentral) (hK : KFacts.KS12NormalizerMoves)
    (hK9 : KFacts.KS12OrderNine) (hG1 : Gap125NonCentralBar)
    (hT : Gap127TwoCfg) (hOTwo : KS129OTwo) (hSp : Gap129YSporadic) (hG2R : Gap129YG2Range)
    (hHD4 : Gap129HessD4) (hEE : Gap129EndE) : Sec21.Item129Bar :=
  item129Bar_of_inputs_R h1 h2 h43 hcov hKC h128 hNF h422 h423 h424 hN hST h45 h48 h49 hB3 hK hK9
      hG1 Hering129L.ks129ThreeLocalFix_holds hT (Hering129L.gap127D4Even_of h1) hOTwo
      Hering129L.psl28ProperSolvable_holds hSp hG2R kf_l3_pgl gap129HessL3Deg_holds hHD4 hEE

end CFSG.RankThree.PartTwo.Sec12
