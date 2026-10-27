module

public import CFSG.RankThree.PartOne.S9.Assembly
public import CFSG.RankThree.PartOne.S8.ResidualBound
public import CFSG.RankThree.PartOne.KA.AlternatingComponent
public import CFSG.RankThree.PartOne.KC.LinearCAAdapter
public import CFSG.RankThree.PartOne.KC.OriginalLinearFromInnerPlane
public import CFSG.RankThree.PartOne.KC.OriginalUnitaryAssembly
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
public import CFSG.RankThree.PartOne.KC.UnitaryNonsplitNoninnerPlane
public import CFSG.RankThree.PartOne.KC.UnitaryHigherNoninnerPlane
public import CFSG.RankThree.PartOne.KC.EvenUnitaryFiveAllPlane
public import CFSG.RankThree.PartOne.KC.UnitaryNonsplitInnerPlaneProducts
public import CFSG.RankThree.PartOne.KC.UnitaryHigherInnerPlaneProducts
public import CFSG.RankThree.PartOne.KC.OriginalSymplecticOrthogonalFinal

public section

namespace CFSG.RankThree.PartOne

theorem selectedPrimeDichotomy_of_families (hbridge : TauCetiCatalogBridge)
    (hlin : OriginalLinearComponentLocalCoreOddAction)
    (hunit : OriginalUnitaryComponentLocalCoreOddAction)
    (hsymp : OriginalSymplecticOrthogonalComponentLocalCoreOddAction)
    (hspor : OriginalSporadicComponentLocalCoreOddAction)
    (hexc : OriginalExceptionalComponentLocalCoreOddAction)
    (hcop : OriginalCoprimeCatalogComponentLocalCoreCentralization)
    (halt : AlternatingComponentSelectedPrimeLocalCoreCentralization) :
    SelectedPrimeDichotomy :=
  selectedPrimeDichotomy_of_residualBound
    (sectionEightResidualBound_of_families hbridge hlin hunit hsymp hspor hexc hcop halt)

theorem selectedPrimeDichotomy_of_remaining_families (hbridge : TauCetiCatalogBridge)
    (hlin : OriginalLinearComponentLocalCoreOddAction)
    (hunit : OriginalUnitaryComponentLocalCoreOddAction)
    (hsymp : OriginalSymplecticOrthogonalComponentLocalCoreOddAction)
    (hspor : OriginalSporadicComponentLocalCoreOddAction)
    (hexc : OriginalExceptionalComponentLocalCoreOddAction)
    (hcop : OriginalCoprimeCatalogComponentLocalCoreCentralization) :
    SelectedPrimeDichotomy :=
  selectedPrimeDichotomy_of_families hbridge hlin hunit hsymp hspor hexc hcop
    alternatingComponentSelectedPrimeLocalCoreCentralization

theorem selectedPrimeDichotomy_of_open_families (hbridge : TauCetiCatalogBridge)
    (hspor : OriginalSporadicComponentLocalCoreOddAction)
    (hexc : OriginalExceptionalComponentLocalCoreOddAction)
    (hcop : OriginalCoprimeCatalogComponentLocalCoreCentralization) :
    SelectedPrimeDichotomy :=
  selectedPrimeDichotomy_of_remaining_families hbridge
    (original_linear_component_local_core_odd_action_of_inner_plane
        linear_nonsplit_inner_plane_products_trivial)
    (original_unitary_component_local_core_odd_action_of
        unitary_defining_prime_actual_component_local_core_product_centralizes
        (unitary_nonsplit_inner_actual_component_centralization_of
            unitary_nonsplit_inner_plane_products_trivial)
        (nonsplit_unitary_noninner_actual_component_odd_action_of
            nonsplit_unitary_noninner_plane_local_core_product_odd)
        (higher_unitary_all_plane_actual_component_odd_action_of
            higher_unitary_inner_plane_products_trivial
            higher_unitary_noninner_plane_local_core_product_odd)
        (even_unitary_five_actual_component_local_core_product_odd_action_of
            even_unitary_five_all_plane_local_core_product_odd))
    original_symplectic_orthogonal_component_local_core_odd_action hspor hexc hcop

end CFSG.RankThree.PartOne
