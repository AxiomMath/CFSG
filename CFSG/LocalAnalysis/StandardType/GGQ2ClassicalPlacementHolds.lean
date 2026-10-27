module

public import CFSG.LocalAnalysis.StandardType.GGQ2ClassicalPlacement
public import CFSG.LocalAnalysis.StandardType.GGQ2ClassicalCatalogueU
public import CFSG.LocalAnalysis.StandardType.GGQ2FrameAmbient
import CFSG.LocalAnalysis.StandardType.GGQ2LinPlacementHolds
import CFSG.LocalAnalysis.StandardType.GGQ2UnitPlacementHolds
import CFSG.LocalAnalysis.StandardType.GGQ2SpPlacementHolds
import CFSG.LocalAnalysis.StandardType.GGQ2OrthPlacementHolds

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly

section


theorem placementInputOn_classical_holds (ex : FrameKind → RawFrameData) :
    PlacementInputOn ClassicalLabel (catalogueOf classicalCatalogue ex) :=
  placementInputOn_classical_of_families (placementInputOn_lin_holds ex)
    (placementInputOn_unit_holds ex) (placementInputOn_sp_holds ex)
    (placementInputOn_orth_holds ex)

theorem placementCoreInputOn_classical_holds (ex : FrameKind → RawFrameData) :
    PlacementCoreInputOn ClassicalLabel (catalogueOf classicalCatalogue ex) :=
  placementCoreInputOn_classical_of_families (placementCoreInputOn_lin_holds ex)
    (placementCoreInputOn_unit_holds ex) (placementCoreInputOn_sp_holds ex)
    (placementCoreInputOn_orth_holds ex)

end

end CFSG.StandardType.GGQ2Frame

end
