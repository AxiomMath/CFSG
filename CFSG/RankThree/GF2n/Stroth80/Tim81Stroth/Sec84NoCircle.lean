module

public import CFSG.RankThree.GF2n.Stroth80.Sec84LeavesH
public import CFSG.RankThree.GF2n.Stroth80.Tim81Stroth.UnitaryRootAt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank


theorem sec84LeavesH_of_fields
    (h1 : CFSG.RankThree.GF2n.Tim81.Theorem1Statement)
    (h34 : Stroth34Statement) (h51 : Stroth51Statement) (h53 : Stroth53Statement)
    (h54 : Stroth54Statement) (h82 : Stroth82Statement) (h83 : Stroth83Statement)
    (hNt : StrothNtStatement) (hge : Stroth6NbarGeStatement)
    (h310chi : Stroth310ChiStatement) (aExists : Sec8AExistsStatement)
    (zt : Sec8ZtStatement) (psu6Out : PSU6OutSolvableStatement) :
    Sec84LeavesH :=
  { h34 := h34
    h51 := h51
    h53 := h53
    h54 := h54
    h82 := h82
    h83 := h83
    hNt := hNt
    hge := hge
    h310chi := h310chi
    aExists := aExists
    zt := zt
    tim81SpRoot := tim81StrothSpUnRootStatement_holds_of_inputs h1
      (step85F2_holds h34 h51 aExists zt h54 hge) h51 aExists h34
    psu6Out := psu6Out }

theorem sec84_of_fields
    (h1 : CFSG.RankThree.GF2n.Tim81.Theorem1Statement)
    (h34 : Stroth34Statement) (h51 : Stroth51Statement) (h53 : Stroth53Statement)
    (h54 : Stroth54Statement) (h82 : Stroth82Statement) (h83 : Stroth83Statement)
    (hNt : StrothNtStatement) (hge : Stroth6NbarGeStatement)
    (h310chi : Stroth310ChiStatement) (aExists : Sec8AExistsStatement)
    (zt : Sec8ZtStatement) (psu6Out : PSU6OutSolvableStatement) :
    Stroth84Statement ∧ Stroth85Statement ∧ Stroth86Statement :=
  sec84_of_leavesH
    (sec84LeavesH_of_fields h1 h34 h51 h53 h54 h82 h83 hNt hge h310chi aExists zt psu6Out)

end CFSG.RankThree.GF2n.Stroth80
