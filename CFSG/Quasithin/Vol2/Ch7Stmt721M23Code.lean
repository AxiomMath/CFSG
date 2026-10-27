module

public import CFSG.Quasithin.Vol2.Ch7Lem754
public import CFSG.Quasithin.Background.HMathieuCode23

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu
open scoped IsMulCommutative

theorem stmt7_2_1_M23Code :
    Stmt7_2_1_M23Code := by
  intro G _ _ T L I _ hV hNM _ hrow
  have hL : MathieuCode23 (V := IntMod (fsuV T I) hV) (autI hV (fsuL0 T L)) ⊤ ⊥ := hrow
  have hLM : IsOver (autI hV (fsuL0 T L)) (autI hV ⊤) :=
    ⟨autI_fsuL0_le hV, autI_top_le_normalizer hV hNM⟩
  exact ⟨pRank_le_of_card_le fun A hAM hAe k hk => code23_card_le hLM hL hAM hAe hk,
    code23_betaH hLM hL, code23_alphaH hLM hL,
    fun A hAM hAe hcard => code23_xi hLM hL hAM hAe hcard⟩

end CFSG.Quasithin.H13
