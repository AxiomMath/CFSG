module

public import CFSG.RankThree.PartOne.KP.SporadicDefs
public import CFSG.RankThree.SteinbergCBONOuterPrimes

public section

namespace CFSG.RankThree.PartOne

open CFSG
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem sporadicCoprimeRank_ONan : SporadicCoprimeRank .ONan :=
  sporadicCoprimeRank_of_not_dvd_outer fun q hq hq5 hdvd => by
    rcases Quasithin.SteinbergCB.ON_large_prime_outer_automorphisms_absent q hq hdvd with rfl | rfl
    · omega
    · omega

end CFSG.RankThree.PartOne
