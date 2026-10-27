module

public import CFSG.Sporadic.SmallOddCore.Co3GenFitting
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUSporadic

public section

namespace CFSG.Sporadic.SmallOddCore

open CFSG.ComponentClassification.CatalogueU

theorem sporadicOddCoreFree_Co3 : SporadicOddCoreFree .Co3 :=
  fun _ _ _ hF _ hJ t ht =>
    (ctuc_co3_generalized_fitting_centralizers_odd_core_trivial hF hJ).2 t ht

end CFSG.Sporadic.SmallOddCore
