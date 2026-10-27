module

public import CFSG.Monster.SteinbergMGmatUnconditional
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUSporadic

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ComponentClassification.CatalogueU

open CFSG.ComponentClassification.BMCase
  (exact_M_full_original_group_involution_odd_core_unconditional)

theorem sporadicOddCoreFree_M :
    SporadicOddCoreFree .M :=
  fun X _ _ hs hna hiso t ht =>
    ((exact_M_full_original_group_involution_odd_core_unconditional X hs hna hiso).2 t ht).2

end CFSG.ComponentClassification.CatalogueU
