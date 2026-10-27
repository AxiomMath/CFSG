module

public import CFSG.OddTranspositions.PartThree.Nine.FinalAbelian
public import CFSG.OddTranspositions.PartThree.Nine.FinalSuzukiDirect

public section

namespace CFSG.OddTranspositions.PartThree.Nine

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.BenderSuzuki


theorem final9_1_holds : Final9_1 := by
  intro G _ _ D hC hH hs _ h3 T S hTS h4 h5 Q hQ h7
  obtain ⟨U, hU⟩ := exists_deltaSetup hC hH h3 T S hTS
  have hSN : (S : Subgroup G) ≤ Subgroup.normalizer ((fun v => hC.d * v) '' (U : Set G)) :=
    hU.sylow_inter ▸ h4.2.1
  obtain ⟨z, hzU, hz1, hzS⟩ := exists_central_mem_omega h3 hU hSN
  by_cases hW : IsMulCommutative (CFSG.LargeExtraspecial.S11.wcl z)
  · obtain ⟨f, hf, eH, eK, hidx⟩ := minus_of_wcl_abelian hC hH hs h3 h4 h5 hQ hU hzU hz1 hzS hW
    exact ⟨f, hf, eH, Or.inr ⟨eK, hidx⟩⟩
  · exfalso
    rcases hU.model with ⟨f, hf, hUn, ⟨eH⟩⟩ | ⟨m, hm, hUn, ⟨eH⟩⟩ | ⟨f, -, -, ⟨eH⟩⟩
    · exact hU.false_of_wcl_not_commutative_of_psl2 hH h3 h5 hQ h7 (by omega) eH hUn hzU hz1 hW
    · exact hU.false_of_wcl_not_commutative_of_sz_direct hH hs h3 h4 h5 hQ h7 hm eH hUn hzU hz1
        hW
    · exact h5.2 ⟨f, ⟨eH⟩⟩

end CFSG.OddTranspositions.PartThree.Nine
