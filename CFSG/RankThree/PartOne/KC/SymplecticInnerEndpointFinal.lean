module

public import CFSG.RankThree.PartOne.KC.SymplecticInnerEndpoint
public import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizerLayer

public section

namespace CFSG.RankThree.PartOne

theorem symplectic_actual_rank_inner_plane_local_core_product_centralizes :
    SymplecticActualRankInnerPlaneLocalCoreProductCentralizes :=
  symplectic_actual_rank_inner_plane_local_core_product_centralizes_of_full
    fun _ _ _ _ hadm hp hp3 hpℓ K _ _ hK =>
      symplectic_inner_plane_common_centralizer hadm hp hp3 hpℓ K hK

end CFSG.RankThree.PartOne
