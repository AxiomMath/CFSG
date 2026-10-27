module

public import CFSG.RankThree.PartTwo.KFacts.K426Rest
public import CFSG.RankThree.Native.ONThreeCentralizer
public import CFSG.RankThree.Native.ONThreeFusion

public section

namespace CFSG.RankThree.PartTwo.KFacts.K426Rest

open CFSG.RankThree.Native

theorem onThreeCentralizer :
    ONThreeCentralizer := by
  intro x hx
  obtain ⟨k, hk⟩ := onThree_fusion hx orderOf_onThreeElt
  have hx' : x = k⁻¹ * onThreeElt * k := by rw [← hk]; group
  rw [hx', card_centralizer_conj_eq]
  exact card_centralizer_onThreeElt

end CFSG.RankThree.PartTwo.KFacts.K426Rest
