module

public import CFSG.Quasithin.Vol2.Ch12Sec2Inputs
public import CFSG.Quasithin.Vol2.GoldschmidtG2ZornCover

public section

namespace CFSG.Quasithin.H13

theorem g2ZornQuotientModel_holds : G2ZornQuotientModel := by
  intro Q _ _ hQ hZ K _ _ n hK hn φ hφ
  refine ⟨fun h1 => ?_, fun h2 => G2Zorn.lieModel_g2_of_cover hQ hZ h2 hK φ hφ⟩
  subst h1
  exact G2Zorn.lieModel_psu_of_cover hQ (by simpa using hK) φ hφ

end CFSG.Quasithin.H13
