module

public import CFSG.Sporadic.Schreier.LyOddCoreAll
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUSporadic

public section

namespace CFSG.Sporadic.LySchreier

theorem sporadicOddCoreFree_Ly : CFSG.ComponentClassification.CatalogueU.SporadicOddCoreFree .Ly :=
  fun _ _ _ hF hnab hJ t ht => (full_group_all_involution_odd_core hF hnab hJ).2 t ht

end CFSG.Sporadic.LySchreier
