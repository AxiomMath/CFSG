module

public import CFSG.Quasithin.H13.NQCatKG68Inner
public import CFSG.Quasithin.H13.KGFact68L2p
public import CFSG.Quasithin.H13.KGFact68J4Cyc
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporAutMain
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J4OutFinal

public section

namespace CFSG.Quasithin.H13.KG68

open CFSG.QuasithinUnique CFSG.Quasithin

theorem e68ComponentFactsSpor_holds :
    E6.E68ComponentFactsSpor :=
  e68ComponentFactsSpor_of
    (Ch1.sporadicAutInner_of_residual (Ch1.sporadicResidualAutInner_of_rest
      (Ch1.sporadicRestAutInner_of_J4OutOdd Setup.X1.j4OuterOdd)))
    sporadicSylowCenterCyclic_holds

theorem e68ComponentFacts_holds :
    E6.E68ComponentFacts :=
  E6.e68ComponentFacts_of_cases e68ComponentFactsLie_holds e68ComponentFactsCover_holds
    e68ComponentFactsAlt_holds e68ComponentFactsL2p_holds e68ComponentFactsSpor_holds

end CFSG.Quasithin.H13.KG68
