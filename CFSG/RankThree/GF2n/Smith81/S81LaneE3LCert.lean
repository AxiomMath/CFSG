module

public import CFSG.RankThree.GF2n.Smith81.S81R213Main
public import CFSG.RankThree.GF2n.Smith81.S81RD8Main
public import CFSG.RankThree.GF2n.Smith81.S81JFe1
public import CFSG.RankThree.GF2n.Smith81.S81JFe2
public import CFSG.RankThree.GF2n.Stroth80.Sec12Certified
public import CFSG.RankThree.GF2n.Stroth80.Sec34ClassicalProof

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

section Certs

theorem laneE3L_certified :
    Smith24E3LUniformStatement ∧ E3LRootEltStatement ∧ Smith212ENonfusedE3LStatement ∧
      Smith213E3LStatement ∧ Smith216ECountE3LStatement ∧ Smith28E3LStatement := by
  have h34 : Stroth34Statement := stroth34Statement_unconditional
  have hFE1 : Smith24E3LUniformStatement :=
    smith24E3LUniform_of_inputs h34 strothGenByBStatement_certified
  have hFE2 : E3LRootEltStatement := e3lRootElt_of_inputs hFE1 h34
  obtain ⟨hNF, hCount, h28⟩ := laneE3L_of_fe1 hFE1 h34
  exact ⟨hFE1, hFE2, hNF, E3LRoot.smith213E3L_of_inputs hFE1 hFE2 hNF
      (E3LRoot.smith212E3LRoot_of_inputs hFE1 hFE2 hNF)
      (E3LRoot.e3lD8Centre_of_inputs hFE1 hFE2 hNF), hCount, h28⟩

end Certs

end CFSG.RankThree.GF2n.Smith81
