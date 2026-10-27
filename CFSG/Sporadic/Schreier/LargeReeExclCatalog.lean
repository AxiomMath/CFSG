module

public import CFSG.Sporadic.Schreier.LargeReeExcl
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUAlmostSimple

public section

namespace CFSG.Sporadic.Schreier.LargeReeExcl

theorem CTU_catalog_large_Ree_Tits_check_holds :
    CFSG.ComponentClassification.CatalogueU.LargeReeTitsCheck :=
  fun X _ _ hs hn t f ht hm hz => absurd hz (CTU_catalog_large_Ree_Tits_check X hs hn t f ht hm)

end CFSG.Sporadic.Schreier.LargeReeExcl
