module

public import CFSG.Quasithin.Vol2.GoldschmidtF431G2F48Main

public section

namespace CFSG.Quasithin.H13.F431.G2

open CFSG.Blueprint CFSG.Quasithin.H13.F431


theorem f431Recognition_g2_of_f48 (f : ℕ) (h48 : F431F48 .G2 0 f (f431ModelFacts_g2 f)) :
    F431Recognition .G2 0 f :=
  recognition_of_facts (f431ModelFacts_g2 f) (f431Generation_g2 f) (polyNumber .G2)
    (three_le_polyNumber _) (f431Facts45_g2 f (f431ModelFacts_g2 f)) h48

theorem f431Recognition_g2 (f : ℕ) : F431Recognition .G2 0 f :=
  f431Recognition_g2_of_f48 f (F48.f431F48_g2 f (f431ModelFacts_g2 f))

end CFSG.Quasithin.H13.F431.G2
