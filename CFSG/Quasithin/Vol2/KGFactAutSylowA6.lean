module

public import CFSG.Quasithin.Vol2.Ch3Sec3InspA312
public import CFSG.Quasithin.Vol2.KGFactAutSylowSmall

public section

namespace CFSG.Quasithin.H13.KGAutSyl

theorem factAutSylowA6_holds : FactAutSylowA6 := by
  intro Q _ _ hQ
  rcases hQ with h | h
  · obtain ⟨e⟩ := h
    exact autSylowSelfNorm_of_equiv_alt6 e
  · obtain ⟨e⟩ := CFSG.QuasithinUnique.Setup.Family.alternating_six_of_model_nine h
    exact autSylowSelfNorm_of_equiv_alt6 e

end CFSG.Quasithin.H13.KGAutSyl
