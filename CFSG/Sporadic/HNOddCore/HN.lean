module

public import CFSG.Sporadic.HNOddCore.GenFitting
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUSporadic

public section

namespace CFSG.Sporadic.HNOddCore

theorem sporadicOddCoreFree_HN :
    CFSG.ComponentClassification.CatalogueU.SporadicOddCoreFree .HN :=
  fun _ _ _ hF _ hJ t ht => (ctuc_hn_generalized_fitting_involution_centralizer_odd_core_trivial
    hF hJ).2 t ht

end CFSG.Sporadic.HNOddCore
