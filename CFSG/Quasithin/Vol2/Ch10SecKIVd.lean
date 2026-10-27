module

public import CFSG.Quasithin.Vol2.Ch10SecKIVc

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10KH.KIV

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique


theorem kgTwoA5Generate_holds : KGTwoA5Generate := by
  intro Y _ _ T hT B₁ hB₁ B₂ hB₂ h₁ h₂ hne
  refine ⟨fun h => ?_, fun hJ => Or.inl (sup_eq_top_J1 hJ hT hB₁ hB₂ h₁ h₂ hne)⟩
  rcases h with ⟨p, hp, -, hp8, hY⟩ | hY
  · exact sup_eq_top_psl2_prime hp (by rintro rfl; omega) hY h₁ h₂ hne
  · exact sup_eq_top_psl2_25 hY h₁ h₂ hne

end CFSG.Quasithin.Vol2.Ch10.SecB.C10KH.KIV
