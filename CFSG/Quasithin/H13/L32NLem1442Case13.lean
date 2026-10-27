module

public import CFSG.Quasithin.H13.L32NLem1442p
public import CFSG.Quasithin.H13.L32NLem1442x
public import CFSG.Quasithin.H13.L32NM22Facts
public import CFSG.Quasithin.Background.HM22Recog

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

theorem case1442FromConcl13S_of
    (h12213 : Stmt12_2_13) : Case1442FromConcl13S := by
  intro G _ _ T L V V₂ g a D C c13
  obtain ⟨e, he⟩ := CFSG.Quasithin.H.Mathieu.M22Link.exists_linearEquiv_m22_of_normal
    c13.1.1 c13.1.2 c13.2.2
  exact C.case6_of_model h12213 c13 he
    (fun E hE hsq => CFSG.Quasithin.H13.M22Facts.m22_card_le hE hsq)
    (fun hQ' hB' hinv => CFSG.Quasithin.H13.M22Facts.m22_quad_unique hQ' hB' hinv)

end CFSG.Quasithin.H13
