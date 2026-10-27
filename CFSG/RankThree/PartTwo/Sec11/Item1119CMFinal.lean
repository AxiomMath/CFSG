module

public import CFSG.RankThree.PartTwo.Sec11.Item1120R1
public import CFSG.RankThree.PartTwo.Sec11.Item1119SymFinal
public import CFSG.RankThree.PartTwo.Sec11.Item1119R2Split
public import CFSG.RankThree.PartTwo.Sec11.Item1119R2Item111
public import CFSG.RankThree.PartTwo.Sec11.Item1119CMCore
public import CFSG.RankThree.PartTwo.Sec11.Item1119NLMain
import CFSG.RankThree.PartTwo.Sec11.Item1117Res3ProofCommL3
import CFSG.RankThree.PartTwo.Sec11.Item1118Res2Proof
import CFSG.RankThree.PartTwo.Sec11.Item1118Res3Proof

public section

namespace CFSG.RankThree.PartTwo.Sec11

section Certified


theorem sym1119YAlphaComm_holds
    (h113 : Item113) (h117 : Item117) (h118 : Item118)
    (h119 : Item119) (hNum : Sym1119Numbers) : Sym1119YAlphaComm :=
  sym1119YAlphaComm_of Sec4.rank3II_4_5 h113 h117 (item1120_of_standing h113 h117 h118 h119)
    (step1119Comm_of (step1119CommG2_of_model Sec4.rank3II_4_5 h117)
      (step1119CommD4_of_basic Sec4.rank3II_4_5 h117) (step1119CommL3_holds h117))
    (sym1119YAlphaSplit_holds Sec4.rank3II_4_5 h119) hNum sym1119NotLThree_holds

theorem step1119SymTypes_of_standing_comm
    (h113 : Item113) (h117 : Item117) (h118 : Item118)
    (h119 : Item119) (hNum : Sym1119Numbers) : Step1119SymTypes :=
  step1119SymTypes_holds Sec4.rank3II_4_5 h113 h117 (item1120_of_standing h113 h117 h118 h119)
      (sym1119YAlphaSplit_holds Sec4.rank3II_4_5 h119)
      (sym1119YAlphaComm_holds h113 h117 h118 h119 hNum) hNum sym1119NotLThree_holds
      (sym1119Item111_holds Sec4.rank3II_4_5 h113 h117)

end Certified

end CFSG.RankThree.PartTwo.Sec11
