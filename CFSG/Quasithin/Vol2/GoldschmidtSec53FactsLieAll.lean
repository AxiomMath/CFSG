module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModG2
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModD4Main
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModF4
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModU4
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModU5
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsU5Main
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsG2

public section

namespace CFSG.Quasithin.H13.Sec53F

set_option linter.unusedSectionVars false

section G2


theorem lieFactsAt_g2 : LieFactsAt .G2 0 := And.intro G2.lieModelFacts_g2 G2.lieAutFacts_g2

end G2

section D4


theorem lieFactsAt_d4 : LieFactsAt .trialityD4 0 := And.intro lieModelFacts_d4 lieAutFacts_d4

end D4

section F4


theorem lieFactsAt_f4 : LieFactsAt .twistedF4 0 := And.intro lieModelFacts_f4 lieAutFacts_f4

end F4

theorem lieFactsAt_u4 : LieFactsAt .PSU 4 := And.intro lieModelFacts_u4 lieAutFacts_u4

theorem lieFactsAt_u5 : LieFactsAt .PSU 5 := And.intro lieModelFacts_u5 lieAutFacts_u5

end CFSG.Quasithin.H13.Sec53F
