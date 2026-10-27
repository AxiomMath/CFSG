module

public import CFSG.RankThree.PartTwo.Sec15.Item1520StepsProofComm
public import CFSG.RankThree.PartTwo.Sec15.Item1520StepsProofConj
public import CFSG.RankThree.PartTwo.Sec15.Item1520StepsProofHess
public import CFSG.RankThree.PartTwo.Sec15.Item1520StepsProofCore

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec17

theorem step1520R_of_named (h1423 : Item14_23R) (h1517 : Step1517R) (h138 : Item138N)
    (hK : KS1520HessCent) (hcomp : Step1520CoreComp) : Step1520R :=
  step1520R_of h1423 (step1520Core_of (step1520Comm_of h1517 h138 hK) hcomp)
    (step1520Comm_of h1517 h138 hK)

theorem step1522Hyp_of_hessSub (h1517 : Step1517R) (h1518 : Step1518R) (h138 : Item138N)
    (hHS : KS1522HessSub) (hl34 : Step1522HypNotL34) : Step1522Hyp :=
  step1522Hyp_of h1518 h138 (step1522HypMeet_of_hessSub h1517 h1518 h138 hHS) hl34

theorem step1522R_of_named (h1424 : Item14_24R) (h153 : Item153MainR) (h1517 : Step1517R)
    (h1518 : Step1518R) (h138 : Item138N) (hl34 : Step1522HypNotL34) (hHS : KS1522HessSub)
    (hT : KS1522TorusMeet) (hH : KS1522HessTrans) : Step1522R :=
  step1522R_of h1424 h153 h1517 (step1522Hyp_of_hessSub h1517 h1518 h138 hHS hl34)
    (step1522Conj_of h1517 h138 hT hH)

end CFSG.RankThree.PartTwo.Sec15
