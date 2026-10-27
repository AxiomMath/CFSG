module

public import CFSG.OddTranspositions.PartThree.Nine.NineFiveE
public import CFSG.OddTranspositions.PartThree.Nine.FiveUnitaryEnd

public section

namespace CFSG.OddTranspositions.PartThree.Nine


theorem lemma9_5 (h87 : Theorem8_7) : Lemma9_5 := by
  intro G _ _ D hC hH hs hIH h3 T S hTS h4
  have hCH := centralizer_Halpha_eq_zpowers h87 hC hH h3
  have hU3 := not_exists_mulEquiv_psu3 hC hH hs hIH h3 T S hTS h4 hCH
  unfold Conclusion9_5
  exact ⟨centralizer_inter_eq_sylow_map_of_not_psu3 hC hH h3 T S h4 hCH hU3, hU3⟩

end CFSG.OddTranspositions.PartThree.Nine
