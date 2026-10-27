module

public import CFSG.RankThree.GF2n.Stroth80.Sec8StepsAssembly
public import CFSG.RankThree.GF2n.Stroth80.Sec8HMain
public import CFSG.RankThree.GF2n.Stroth80.Sec8TypeCount
public import CFSG.RankThree.GF2n.Stroth80.Sec8Canon
public import CFSG.RankThree.GF2n.Stroth80.Sec8StepsCommN
public import CFSG.RankThree.GF2n.Stroth80.Sec8StepsDPrime
public import CFSG.RankThree.GF2n.Stroth80.Sec8StepsLemmaD
public import CFSG.RankThree.GF2n.Stroth80.Sec8StepsSylow

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem stroth81_of_inputs' (h34 : Stroth34Statement) (h310chi : Stroth310ChiStatement)
    (hRoot : Stroth310RootStatement) (h311b : Stroth311bCommStatement) (h51 : Stroth51Statement)
    (h53 : Stroth53Statement) (hA : Sec8AExistsStatement) (hzt : Sec8ZtStatement)
    (hF : Close8FinalStatement) : Stroth81Statement := by
  have hCanon := sec8Canon_of h34 hRoot
  have hT := sec8TypeCount_of h34 hRoot h53 h310chi
  have hH := sec8LemmaH_of h34 hRoot h51 h53 h310chi
  have hZV := sec8ZV_of_inputs h51 hA hzt h310chi
  have hTI := sec8TI_of_inputs h51 hA hzt h310chi
  have hD := sec8LemmaD_of h310chi h53.1
  have hD' := sec8DPrime_of h51 hA sec8PointsTrans_holds sec8PointTI_of
  have hV := step81Vanish_of hCanon hD' (sec8Invol_of h310chi h53.1) h310chi h53
  exact stroth81_of_steps hV (step81Type_of hCanon hT hV)
    (step81close_of_parts (close81E_of hD hD' (sec8CommN_of_311 h34 hRoot h311b))
      (close81Sylow_of h34 h310chi h51 h53 hA hTI hZV sec8PointTI_of hD hD' hH) hTI hF)

end CFSG.RankThree.GF2n.Stroth80
