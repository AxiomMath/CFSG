module

public import CFSG.LocalAnalysis.StandardType.GGSporKOrdBMRows
public import CFSG.LocalAnalysis.StandardType.GGSporKOrdersB
public import CFSG.LocalAnalysis.StandardType.GGSporKOrdersM

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.Open
  CFSG.EvenSmallLie.CatalogOrders

theorem bmOrd_B_three [Finite (TauCeti.CFSGIndex.sporadic .B).Group] :
    BMOrd 3 (TauCeti.CFSGIndex.sporadic .B).Group := by
  refine bmOrd_of_rows 3 4154781481226426191177580544000000 ggSporK_card_sporadicB
    (fun lab hlab hd => ?_)
  rw [ordBM_factorization_B_three]
  exact ordBMRow_of_search (by norm_num) (by norm_num) (by norm_num)
    (bmLieSearch_mono (fun t n q o h => by simp only [Bool.or_eq_true, Bool.and_eq_true] at h ⊢; tauto) ordBM_search_B)
    ordBM_twF4_B (by decide) (by decide) (by decide) lab hlab hd

theorem bmOrd_B_five [Finite (TauCeti.CFSGIndex.sporadic .B).Group] :
    BMOrd 5 (TauCeti.CFSGIndex.sporadic .B).Group := by
  refine bmOrd_of_rows 5 4154781481226426191177580544000000 ggSporK_card_sporadicB
    (fun lab hlab hd => ?_)
  rw [ordBM_factorization_B_five]
  exact ordBMRow_of_search (by norm_num) (by norm_num) (by norm_num)
    (bmLieSearch_mono (fun t n q o h => by simp only [Bool.or_eq_true, Bool.and_eq_true] at h ⊢; tauto) ordBM_search_B)
    ordBM_twF4_B (by decide) (by decide) (by decide) lab hlab hd


end CFSG.StandardType.SporadicShape
