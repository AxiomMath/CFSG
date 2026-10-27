module

public import CFSG.RankThree.GF2n.Stroth80.OpenSectionsOrder
public import CFSG.RankThree.GF2n.Stroth80.Sec54StatementFinal
public import CFSG.RankThree.GF2n.Stroth80.Sec64RecogMain
public import CFSG.RankThree.GF2n.Stroth80.Sec7Stroth78Holds
public import CFSG.RankThree.GF2n.Stroth80.Sec83MainIntegratedB
public import CFSG.RankThree.GF2n.Stroth80.Sec83SevenHolds
public import CFSG.RankThree.GF2n.Stroth80.Sec8Final
public import CFSG.RankThree.GF2n.Smith81.Stroth4iBridge
public import CFSG.RankThree.GF2n.Stroth80.Sec78CommWtSp

public section

namespace CFSG.RankThree.GF2n.Stroth80

section Certs

theorem strothOpenSectionsOT_of_remaining (h716 : Stroth716TypeStatement)
    (h717 : Stroth717Statement) (h86 : Stroth86Statement) (h98 : Stroth98Statement)
    (h108 : Stroth108Statement) (h1111 : Stroth1111Statement) : StrothOpenSectionsOT :=
  have h34 : Stroth34Statement := stroth34Statement_unconditional
  have h310 : Stroth310Statement := stroth310Statement_unconditional
  have h311a : Stroth311aStatement := stroth311aStatement_unconditional
  have h51 : Stroth51Statement := stroth51Statement_unconditional
  have h53 : Stroth53Statement := stroth53Statement_unconditional
  have h54 : Stroth54Statement := stroth54Statement_holds
  have hA : Sec8AExistsStatement := sec8AExistsStatement_holds
  have hPts : Sec5NatPointsSpStatement := sec5NatPointsSpStatement_unconditional
  have hge : Stroth6NbarGeStatement := stroth6NbarGeStatement_holds
  have h310chi : Stroth310ChiStatement := stroth310Chi_of_34 h34
  have hzt : Sec8ZtStatement :=
    sec8Zt_of_inputs h34 h51 hA (sec8CommWt_of_53 h34 h53 hA hPts) stroth56Sp_holds
  have hF : Close8FinalStatement :=
    close8Final_of_parts h34 h310chi h51 hA hzt h311a stroth44Statement_unconditional
      stroth45Statement_unconditional h54 hge
  have h82 : Stroth82Statement :=
    stroth82_of_inputs_final h34 h310chi (stroth310Root_of_34 h34)
      (stroth311bComm_of_34 h34 h310 h311a) h51 h53 hA hzt hF
  { h65 := stroth65Statement_of_64 h54
      (stroth64_of_corB
        (CFSG.CGT.Timmesfeld75.corollaryBStmt_of_theoremAStmt
          CFSG.CGT.Timmesfeld75.theoremAStmt_holds))
    h78 := stroth78Statement_holds
    h79 := stroth79Statement_holds
    h716 := h716
    h717 := h717
    h83 := stroth83_of_53_only'' h53 h54 h82
    h86 := h86
    h98 := h98
    h108 := h108
    h1111 := h1111
    ci4 := CFSG.RankThree.GF2n.Smith81.stroth4i_holds
    nbarGe := hge }

end Certs

end CFSG.RankThree.GF2n.Stroth80
