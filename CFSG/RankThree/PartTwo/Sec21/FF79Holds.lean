module

public import CFSG.RankThree.PartTwo.Sec21.FF79HoldsSec4
public import CFSG.RankThree.PartTwo.Sec21.FF79ThmA5Final
public import CFSG.RankThree.PartTwo.Sec21.FF79KLemmaOPHolds
public import CFSG.RankThree.PartTwo.Sec21.FF79KLemmaOExcHolds
public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3AS4
public import CFSG.RankThree.PartTwo.Sec21.FF79KTypeLnAlphaSL

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21


theorem ff79TheoremA_simpleK5_holds
    : FF79TheoremA_simpleK5 :=
  ff79TheoremA_simpleK5_of (ff79KLemmaOP_holds ff79KLemmaOExc_holds) ff79AStarExists_holds

theorem ff79Extraspecial_holds
    : FF79Extraspecial :=
  ff79Extraspecial_of_thmA5 ff79KCentAlpha_holds ff79TheoremA_simpleK5_holds

end CFSG.RankThree.PartTwo.Sec21.FF79
