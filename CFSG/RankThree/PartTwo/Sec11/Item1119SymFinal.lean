module

public import CFSG.RankThree.PartTwo.Sec11.Item1119SymAYRefine

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Main


theorem step1119SymTypes_holds (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (h1120 : Item1120) (hSplit : Sym1119YAlphaSplit) (hComm : Sym1119YAlphaComm)
    (hNum : Sym1119Numbers) (hL3 : Sym1119NotLThree) (hK111 : Sym1119Item111) :
    Step1119SymTypes :=
  step1119SymTypes_of_lines_ay h113 h117
    (step1119Lines_holds h45 h113 h117 h1120 hNum hL3 hK111)
    (step1119AY_holds h45 h113 h117 hNum hL3 hSplit hComm)

end Main

end CFSG.RankThree.PartTwo.Sec11

end
