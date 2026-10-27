module

public import CFSG.RankThree.GF2n.Stroth80.Sec8StepsNorm
public import CFSG.RankThree.GF2n.Stroth80.Sec8EndMain

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem sec8ZV_of_inputs (h51 : Stroth51Statement) (hA : Sec8AExistsStatement)
    (hzt : Sec8ZtStatement) (h310chi : Stroth310ChiStatement) : Sec8ZVStatement := by
  intro G _ _ M Q Z B hc n t hs Z0 hZ0 u hu huQ
  exact sec8_ZV_of_parts h51 hA hzt h310chi hc hs hZ0 hu huQ

theorem sec8TI_of_inputs (h51 : Stroth51Statement) (hA : Sec8AExistsStatement)
    (hzt : Sec8ZtStatement) (h310chi : Stroth310ChiStatement) : Sec8TIStatement :=
  sec8TI_of (sec8ZV_of_inputs h51 hA hzt h310chi)

end CFSG.RankThree.GF2n.Stroth80
