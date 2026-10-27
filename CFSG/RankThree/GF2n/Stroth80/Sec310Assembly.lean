module

public import CFSG.RankThree.GF2n.Stroth80.Sec310Main
public import CFSG.RankThree.GF2n.Stroth80.Sec310SLDirect
public import CFSG.RankThree.GF2n.Stroth80.Sec310Symp

public section

namespace CFSG.RankThree.GF2n.Stroth80


theorem stroth310SLBranch_of_34 (h34 : Stroth34Statement) : Stroth310SLBranchStatement :=
  stroth310SLBranch_of_transv (stroth310SLTransv_of_34 h34)

theorem stroth310_of_34 (h34 : Stroth34Statement) (hCl : Stroth310ClassifyStatement) :
    Stroth310Statement :=
  stroth310_of_steps h34 (stroth310SLBranch_of_34 h34) (stroth310SympForm_of_34 h34) hCl

end CFSG.RankThree.GF2n.Stroth80
