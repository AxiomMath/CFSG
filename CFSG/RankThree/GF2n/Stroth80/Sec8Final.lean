module

public import CFSG.RankThree.GF2n.Stroth80.Sec8Inputs
public import CFSG.RankThree.GF2n.Stroth80.Sec8Close82
public import CFSG.RankThree.GF2n.Stroth80.Sec8StepsClose82

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem stroth82_of_inputs_final (h34 : Stroth34Statement) (h310chi : Stroth310ChiStatement)
    (hRoot : Stroth310RootStatement) (h311b : Stroth311bCommStatement) (h51 : Stroth51Statement)
    (h53 : Stroth53Statement) (hA : Sec8AExistsStatement) (hzt : Sec8ZtStatement)
    (hF : Close8FinalStatement) : Stroth82Statement :=
  stroth82_of_81a hA (stroth81_of_inputs' h34 h310chi hRoot h311b h51 h53 hA hzt hF)
    (close82False_of_inputs h34 hRoot h51 h53 h310chi hA hzt)

end CFSG.RankThree.GF2n.Stroth80
