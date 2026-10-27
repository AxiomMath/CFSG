module

public import CFSG.RankThree.PartTwo.Sec15.Item1520StepsProof
public import CFSG.RankThree.PartTwo.Sec15.KSL3TwoProofHess
public import CFSG.RankThree.PartTwo.Sec15.KSL3TwoProofTorus
public import CFSG.RankThree.PartTwo.Sec15.KSL3TwoProofOut
public import CFSG.RankThree.PartTwo.Sec15.Item1520StepsProofGen

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec17

theorem step1520Comm_of_item138N (h1517 : Step1517R) (h138 : Item138N) : Step1520Comm :=
  step1520Comm_of h1517 h138 ks1520HessCent

theorem step1521Gen_of_step1517R (h1517 : Step1517R) : Step1521Gen :=
  step1521Gen_of h1517 ks1521TorusCent

theorem step1522Conj_of_item138N (h1517 : Step1517R) (h138 : Item138N) : Step1522Conj :=
  step1522Conj_of h1517 h138 ks1522TorusMeet ks1522HessTrans

theorem step1522HypMeet_of_item138N (h1517 : Step1517R) (h1518 : Step1518R)
    (h138 : Item138N) : Step1522HypMeet :=
  step1522HypMeet_of_hessSub h1517 h1518 h138 ks1522HessSub

theorem step1520R_of_kfacts (h1423 : Item14_23R) (h1517 : Step1517R) (h138 : Item138N)
    (hcomp : Step1520CoreComp) : Step1520R :=
  step1520R_of_named h1423 h1517 h138 ks1520HessCent hcomp

theorem step1522R_of_kfacts (h1424 : Item14_24R) (h153 : Item153MainR) (h1517 : Step1517R)
    (h1518 : Step1518R) (h138 : Item138N) (hl34 : Step1522HypNotL34) : Step1522R :=
  step1522R_of_named h1424 h153 h1517 h1518 h138 hl34 ks1522HessSub ks1522TorusMeet
    ks1522HessTrans

end CFSG.RankThree.PartTwo.Sec15
