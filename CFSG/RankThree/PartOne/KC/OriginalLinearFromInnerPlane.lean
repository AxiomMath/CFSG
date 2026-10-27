module

public import CFSG.RankThree.PartOne.KC.OriginalLinearAssembly
public import CFSG.RankThree.PartOne.KC.LinearPlaneEndpoints
public import CFSG.RankThree.PartOne.KC.LinearDefiningComponent
public import CFSG.RankThree.PartOne.KC.LinearTwoNormalized
public import CFSG.RankThree.PartOne.KC.LinearNoninnerPlaneNonsplit
public import CFSG.RankThree.PartOne.KC.LinearNoninnerPlaneBelowPrime
public import CFSG.RankThree.GroupTheory.SteinbergCELinearTwoPlaneCore

public section

namespace CFSG.RankThree.PartOne

theorem linear_two_plane_core_input : LinearTwoPlaneCoreInput := by
  intro ℓ f hℓ K _ hK B hGB hBE p hp hp3 A hA hAcard a haA ha1
  obtain ⟨-, hodd, hbot, hdiv, -⟩ :=
    CFSG.RankThree.LinearTwoPlaneCore.linear_two_plane_local_core_product_odd hℓ hK hGB hBE hp hp3
      hA hAcard haA ha1
  exact ⟨hodd, hbot, fun hpℓ => (hdiv hpℓ).2.1⟩

theorem original_linear_component_local_core_odd_action_of_inner_plane
    (h5 : LinearNonsplitInnerPlaneProductsTrivial) : OriginalLinearComponentLocalCoreOddAction :=
  original_linear_component_local_core_odd_action_of
      (linear_defining_prime_actual_component_local_core_product_centralizes_of
          (linear_two_normalized_component_local_core_product_odd_image_of
              linear_two_plane_core_input))
      (linear_two_normalized_component_local_core_product_odd_image_of linear_two_plane_core_input)
      (linear_nonsplit_inner_actual_component_centralization_of h5)
      (nonsplit_linear_noninner_actual_component_odd_action_of
          nonsplit_linear_noninner_plane_local_core_product_odd)
      (linear_below_prime_noninner_or_split_normalized_component_odd_action_of
          linear_below_prime_noninner_plane_local_core_product_odd)

end CFSG.RankThree.PartOne
