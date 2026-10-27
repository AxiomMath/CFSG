module

public import CFSG.LocalAnalysis.StandardType.GGSporKOrdBMRows
public import CFSG.LocalAnalysis.StandardType.GGSporKOrdersB
public import CFSG.LocalAnalysis.StandardType.GGSporKOrdersM

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.Open
  CFSG.EvenSmallLie.CatalogOrders

theorem bmOrd_M_seven [Finite (TauCeti.CFSGIndex.sporadic .M).Group] :
    BMOrd 7 (TauCeti.CFSGIndex.sporadic .M).Group := by
  refine bmOrd_of_rows 7 808017424794512875886459904961710757005754368000000000 ggSporK_card_sporadicM
    (fun lab hlab hd => ?_)
  rw [ordBM_factorization_M_seven]
  exact ordBMRow_of_search (by norm_num) (by norm_num) (by norm_num)
    (bmLieSearch_mono (fun t n q o h => by simp only [Bool.or_eq_true, Bool.and_eq_true] at h ⊢; tauto) ordBM_search_M)
    ordBM_twF4_M (by decide) (by decide) (by decide) lab hlab hd

theorem bmOrd_M_thirteen [Finite (TauCeti.CFSGIndex.sporadic .M).Group] :
    BMOrd 13 (TauCeti.CFSGIndex.sporadic .M).Group := by
  refine bmOrd_of_rows 13 808017424794512875886459904961710757005754368000000000 ggSporK_card_sporadicM
    (fun lab hlab hd => ?_)
  rw [ordBM_factorization_M_thirteen]
  exact ordBMRow_of_search (by norm_num) (by norm_num) (by norm_num)
    (bmLieSearch_mono (fun t n q o h => by simp only [Bool.or_eq_true, Bool.and_eq_true] at h ⊢; tauto) ordBM_search_M)
    ordBM_twF4_M (by decide) (by decide) (by decide) lab hlab hd


end CFSG.StandardType.SporadicShape
