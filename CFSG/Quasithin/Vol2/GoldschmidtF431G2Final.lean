module

public import CFSG.Quasithin.Vol2.GoldschmidtF431G2Main
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2Std

public section

namespace CFSG.Quasithin.H13.F431.G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.H13
  CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.F431.Lift


theorem f431Rank2At_g2_of_out
    (hOutLie : ∀ f : ℕ, 2 ≤ f → F431TwoOutLieProp .G2 0 f) : F431Rank2At .G2 0 :=
  f431Rank2At_g2_of_std hOutLie fun _ hf K _ _ _ hK => g2_std hf K hK

end CFSG.Quasithin.H13.F431.G2
