module

public import CFSG.Quasithin.Vol2.Ch7Lem754
public import CFSG.Quasithin.H13.A5M12Chain

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H13.A5.M12
open scoped IsMulCommutative

theorem stmt7_2_1_M12 :
    Stmt7_2_1_M12 := by
  intro G _ _ T L I _ hV hNM _ hrow
  have hL : M12Ten (V := IntMod (fsuV T I) hV) (autI hV (fsuL0 T L)) ⊤ ⊥ := hrow.1
  have hLM : IsOver (autI hV (fsuL0 T L)) (autI hV ⊤) :=
    ⟨autI_fsuL0_le hV, autI_top_le_normalizer hV hNM⟩
  exact ⟨m12_card hL, pRank_le_of_card_le fun A hAM hAe k hk => m12_card_le hLM hL hAM hAe hk,
    m12_betaH hLM hL, m12_alphaH hLM hL, fun A hAM hAe hcard => m12_E16 hLM hL hAM hAe hcard⟩

end CFSG.Quasithin.H13
