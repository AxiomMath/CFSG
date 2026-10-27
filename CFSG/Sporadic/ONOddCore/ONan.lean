module

public import CFSG.Sporadic.ONOddCore.Head
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUSporadic

public section

namespace CFSG.Sporadic.ONOddCore

theorem sporadicOddCoreFree_ONan :
    CFSG.ComponentClassification.CatalogueU.SporadicOddCoreFree .ONan :=
  fun _ _ _ hF _ hJ t ht => (ctuc_on_generalized_fitting_involution_centralizer_odd_core_trivial
    hF hJ).2 t ht

end CFSG.Sporadic.ONOddCore
