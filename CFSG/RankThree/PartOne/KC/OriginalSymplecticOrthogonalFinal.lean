module

public import CFSG.RankThree.PartOne.KC.OriginalSymplecticOrthogonalAssembly
public import CFSG.RankThree.PartOne.KC.SymplecticDefiningComponent
public import CFSG.RankThree.PartOne.KC.OrthogonalInnerPlaneEndpoint
public import CFSG.RankThree.PartOne.KC.SymplecticInnerEndpointFinal
public import CFSG.RankThree.PartOne.KC.SymplecticSubfield
public import CFSG.RankThree.PartOne.KC.OrthogonalNoninnerPlane
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldBY

public section

namespace CFSG.RankThree.PartOne

theorem original_symplectic_orthogonal_component_local_core_odd_action :
    OriginalSymplecticOrthogonalComponentLocalCoreOddAction :=
  original_symplectic_orthogonal_component_local_core_odd_action_of
      symplectic_defining_prime_actual_component_local_core_product_centralizes
      symplectic_actual_rank_inner_plane_local_core_product_centralizes
      (symplectic_noninner_actual_component_odd_action_of
          symplectic_noninner_plane_local_core_product_odd)
      orthogonal_actual_rank_inner_plane_local_core_product_centralizes
      (orthogonal_noninner_actual_component_odd_action_of
          (orthogonal_noninner_plane_local_core_product_odd_of_subfield
              orthogonal_prime_subfield_core_clause_unconditional))

end CFSG.RankThree.PartOne
