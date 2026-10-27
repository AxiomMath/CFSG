module

public import CFSG.RankThree.GF2n.Tim81.GF2nType
public import CFSG.RankThree.GF2n.Smith81.S81Smith1981
public import CFSG.RankThree.GF2n.Stroth80.OpenSectionsRemaining
public import CFSG.RankThree.GF2n.Stroth80.Tim81Stroth.Sec84NoCircle
public import CFSG.RankThree.GF2n.Stroth80.Sec82Holds
public import CFSG.RankThree.GF2n.Stroth80.Sec86PSU6Out

public section

namespace CFSG.RankThree.GF2n.Stroth80

section Sec86

theorem stroth84_85_86_of_thm1 (h1 : CFSG.RankThree.GF2n.Tim81.Theorem1Statement) :
    Stroth84Statement ∧ Stroth85Statement ∧ Stroth86Statement :=
  sec84_of_fields h1 stroth34Statement_unconditional stroth51Statement_unconditional
    stroth53Statement_unconditional stroth54Statement_holds stroth82Statement_holds
    stroth83Statement_holds strothNtStatement_unconditional stroth6NbarGeStatement_holds
    (stroth310Chi_of_34 stroth34Statement_unconditional) sec8AExistsStatement_unconditional
    sec8ZtStatement_holds psu6OutSolvable_holds

theorem stroth86Statement_of_thm1 (h1 : CFSG.RankThree.GF2n.Tim81.Theorem1Statement) :
    Stroth86Statement :=
  (stroth84_85_86_of_thm1 h1).2.2

end Sec86

end CFSG.RankThree.GF2n.Stroth80

namespace CFSG.RankThree.GF2n.Tim81

open CFSG.RankThree.GF2n.Stroth80

section GF2n

theorem gf2nType_of_remaining_thm1
    (h79 : Tim79aStatementWCQ) (h716 : Stroth716TypeStatement)
    (h717 : Stroth717Statement) (h98 : Stroth98Statement) (h108 : Stroth108Statement)
    (h1111 : Stroth1111Statement) : GF2nTypeStatement :=
  have S : StrothOpenSectionsOT := strothOpenSectionsOT_of_remaining h716 h717
    (stroth86Statement_of_thm1 (theorem1Statement_of_inputs h79)) h98 h108 h1111
  have hR : Smith81.Stroth1980Rel :=
    Smith81.stroth1980Rel_of_step fun N hS hM => stroth_order_step_of_open S hS hM
  have hSm : Smith81.Smith1981Statement := Smith81.smith1981_of_rel hR
  gf2nType_of_tim81_inputs h79 (Smith81.stroth1980_of_rel hR hSm) hSm

end GF2n

end CFSG.RankThree.GF2n.Tim81
