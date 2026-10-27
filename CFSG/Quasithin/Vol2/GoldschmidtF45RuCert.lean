module

public import CFSG.Quasithin.Vol2.GoldschmidtF45RuFinal
public import Certificates.Certificate4160

public section

namespace CFSG.Quasithin.H13.F45Ru

theorem f45TwoF4 :
    RuType.F45TwoF4 := by
  have h := Certificates.certificate4160
  obtain ⟨⟨_, _, _, _, _, D₁⟩, ⟨_, _, _, _, _, D₂⟩, -⟩ := h.2.2
  exact facts45L_twoF4_of_oct h.1 D₁ D₂

end CFSG.Quasithin.H13.F45Ru
