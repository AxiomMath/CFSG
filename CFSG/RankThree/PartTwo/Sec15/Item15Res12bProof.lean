module

public import CFSG.RankThree.PartTwo.Sec15.Item15Res12bProofMain
public import CFSG.RankThree.PartTwo.Sec15.Item15Res12bProofK
public import CFSG.RankThree.PartTwo.Sec15.Item15Res12bProofDelta
public import CFSG.RankThree.PartTwo.Sec15.Item15Res12bProofZ

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

theorem item1523R_of_res12b
    (h134 : Item134) (h48 : Sec4.Item4_8) (h142 : Concl142S14)
    (h143 : Concl143S14) (h152 : Item152R) (h1514 : Item1514HJR) (h153 : Item153MainR)
    (h149 : Sec16.Item149S14) (hON : KS1523ONCent) (h155 : Item155HJR)
    (hKR : Step1523KReadY4) (hP : Step1523ZPickY4) (hKS : KS1523HJTwo) : Item1523R :=
  item1523R_of_y4 h1514 h153 h149 hON h155 (step1523KY4R_of_read h143 hKR)
    (step1523DeltaY4R_of_res12b h142 h134 h48)
    (step1523ZY4R_of_res12b' h134 h48 h152 h1514 hP hKS)

end CFSG.RankThree.PartTwo.Sec15
