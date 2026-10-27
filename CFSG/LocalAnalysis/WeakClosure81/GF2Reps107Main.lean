module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps107Defs
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps107Cent
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps107Card
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps107Gen

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)

theorem w4Lem10_7Irr_of_fin (hfin : W4Lem10_7Fin) : W4Lem10_7Irr := by
  intro W _ _ hW Y L t hctx hU hZ htY ht2 hm
  have hcent := w107_commutes_center hW hctx hU htY ht2 hm
  have hcard := w107_card_center_eq_three hW hctx hU hZ ht2 hm hcent
  have hrk := w107_rk_le_fifty_seven hW hctx hU hcard htY ht2 hm
  exact ⟨⟨_, inferInstance, hU, hctx.2.2.2.2.1, hcard, ⟨MulEquiv.refl _⟩⟩,
    hfin W hW Y L t hctx hU hcard hcent hrk htY ht2 hm⟩

end CFSG.LocalAnalysis.WeakClosure81
