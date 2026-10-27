module

public import CFSG.RankThree.PartTwo.Sec15.Item1513StepsProofMeets
public import CFSG.RankThree.PartTwo.Sec15.Item1513StepsProofMax
public import CFSG.RankThree.PartTwo.Sec15.Item1513StepsProofEven
public import CFSG.RankThree.PartTwo.Sec15.Item1513StepsProofList
public import CFSG.RankThree.PartTwo.Sec15.Item1513ProofNoTransv

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14

theorem item1511R_of_steps
    (h158 : Item158Y0R) (hset : Item13SetupAt) (h133 : Item133)
    (h159 : Item159R) (h1510 : Sec15.Item1510R) (hBr : Sec16.Step169TwoBridge)
    (hpt : Step1511Point) (h142 : Item142R) : Item1511R :=
  item1511R_of h158 hset h133 h159 h1510 hBr (step1511List_of hpt h142)

theorem item1513R_of_steps
    (h131 : Item131) (h132 : Item132) (h133 : Item133)
    (h134 : Item134) (h137 : Item137) (h48 : Sec4.Item4_8) (h414 : Sec4.Item4_14_local)
    (h415 : Sec4.Item4_15) (hset : Item13SetupAt) (h146 : Item146S14) (h159 : Item159R)
    (h1510 : Item1510R) (hBr : Sec16.Step169TwoBridge) (h1511 : Item1511R)
    (h1411 : Item1411_1R) (hloc : Claim1411LocalR) (h153 : Item153MainR)
    (hnorm : Claim153NormalR) (hcl : Claim1515M12) (hKf : KS1513Z3PGLOrderThree)
    (hpt : Step1513MeetsPoint) (hJ : Step1513MaxJ) (htype : Step1513EvenType)
    (htrans : Step1513EvenTrans) : Item1513R := by
  have h1511s : Item1511StarR := item1511StarR_of_item1511R h1511
  have hnt : Step1513NoTransv := step1513NoTransv_of h131
  have htv : Step1513Transv := step1513Transv_of h131 h414 hKf
  have hmeets : Step1513Meets := step1513Meets_of h131 h133 h134 h48 h415 h137 hcl h1511s hpt
  have hmax : Step1513Max :=
    step1513Max_of h131 h133 h134 h48 h415 h137 hcl hnt h146 h1511 hpt hJ
  have heven : Step1513Even := step1513Even_of h131 h133 h134 h48 h415 hset hnt htv hmeets hmax
    h1511s h1411 h153 hnorm htype htrans
  exact item1513R_of_named h131 h132 h133 hset h159 h1510 hBr h1511s h1411 hloc h153 hnorm
    (step1513HJ_of h131 h134 h48 h415) hmeets htv hmax heven

end CFSG.RankThree.PartTwo.Sec15
