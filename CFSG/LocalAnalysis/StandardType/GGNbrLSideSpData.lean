module

public import CFSG.LocalAnalysis.StandardType.GGNbrLSideSpElt
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideSpBasic
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideSpInn

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

theorem ggNbrLSideSymplecticData_holds (hDet : GGNbrLSideClsDet)
    (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput) :
    GGNbrLSideSymplecticData := by
  refine ⟨fun ℓ n K _ _ hlam _ hK => ?_, fun ℓ n K _ _ hlam _ hK => ?_,
    fun ℓ n K _ _ _ _ hK => ?_⟩
  · obtain ⟨hn, hℓ, -⟩ := hlam
    exact ggNbrLSideDich_of_elt (ggNbrLSideSp_inn hK hn) (ggNbrLSideSp_center hK)
      (ggNbrLSideSp_elt hDet hO hK hn (Nat.le_trans (by norm_num) hℓ) _)
  · obtain ⟨hn, hℓ, -⟩ := hlam
    exact ggNbrLSideDich_of_elt (ggNbrLSideSp_inn hK hn) (ggNbrLSideSp_center hK)
      (ggNbrLSideSp_elt hDet hO hK hn (Nat.le_trans (by norm_num) hℓ) _)
  · exact ggNbrLSideSp_b2der hK _

end CFSG.StandardType
