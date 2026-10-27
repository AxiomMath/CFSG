module

public import CFSG.RankThree.GF2n.Stroth80.Sec101Gold
public import CFSG.RankThree.GF2n.Stroth80.Sec101Main
public import CFSG.RankThree.GF2n.Stroth80.Unconditional
public import CFSG.RankThree.GF2n.Stroth80.Sec10Assembly
public import CFSG.RankThree.GF2n.Stroth80.Sec10WidthFive
public import CFSG.RankThree.GF2n.Stroth80.Sec103CaseA
public import CFSG.RankThree.GF2n.Stroth80.Sec103CaseB
public import CFSG.RankThree.GF2n.Stroth80.Sec103CaseB2

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem stroth101End_unconditional : Stroth101EndStatement :=
  stroth101End_of stroth34Statement_unconditional stroth44Statement_unconditional
    stroth45Statement_unconditional strothNtStatement_unconditional

theorem stroth101Statement_unconditional : Stroth101Statement :=
  stroth101_of stroth34Statement_unconditional stroth101End_unconditional

theorem stroth103bStatement_of_spread (hspread : StrothNoA2SpreadStatement) :
    Stroth103bStatement :=
  stroth_10_3b_of_cases stroth34Statement_unconditional hspread
    (stroth_10_3_caseA stroth34Statement_unconditional hspread)
    (stroth_10_3_caseB stroth34Statement_unconditional hspread
      (stroth_10_3_caseA stroth34Statement_unconditional hspread))

theorem stroth107_of_103 (hspread : StrothNoA2SpreadStatement) (h103a : Stroth103aStatement)
    (h103b : Stroth103bStatement) : Stroth107Statement :=
  stroth_10_7 stroth34Statement_unconditional stroth311aStatement_unconditional hspread
    stroth101Statement_unconditional h103a h103b
    (stroth107M2Statement_holds stroth34Statement_unconditional
      stroth311aStatement_unconditional hspread)

theorem stroth108_of_103 (hspread : StrothNoA2SpreadStatement) (h103a : Stroth103aStatement)
    (h103b : Stroth103bStatement) (h108 : Stroth108CoreStatement) : Stroth108Statement :=
  stroth108_of_steps stroth101Statement_unconditional h103a h103b
    (stroth107_of_103 hspread h103a h103b) h108

theorem stroth103aStatement_of_spread (hspread : StrothNoA2SpreadStatement) :
    Stroth103aStatement :=
  stroth_10_3a_of_caseB2 stroth34Statement_unconditional hspread
    (stroth_10_3_caseA stroth34Statement_unconditional hspread)
    (stroth107M2Statement_holds stroth34Statement_unconditional
      stroth311aStatement_unconditional hspread)

theorem stroth108Statement_of_spread (hspread : StrothNoA2SpreadStatement)
    (h108 : Stroth108CoreStatement) : Stroth108Statement :=
  stroth108_of_103 hspread (stroth103aStatement_of_spread hspread)
    (stroth103bStatement_of_spread hspread) h108

end CFSG.RankThree.GF2n.Stroth80
