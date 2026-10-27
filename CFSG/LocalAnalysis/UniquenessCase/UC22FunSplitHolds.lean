module

public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitReduction
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitNormalizer
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitInnerModels
import CFSG.GroupTheory.InnerCentralizerProjection

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup

theorem kFunSplit_holds :
    KFunSplit := by
  intro X _ _ _ t n p f hp hp2 hadm hX hA1 hRee P B hB hBc hBo hB3 hBp hperm hrank K hK
  have hBN := normalizes_fundamental_of_permuting X t n p f hp hp2 hadm hX hA1 hRee
    P B hB hBc hBo hB3 hBp hperm hrank K hK
  have hBK : B ≤ K ⊔ centralizer (K : Set X) :=
    CFSG.le_sup_centralizer_of_forall_mem_range_conj hBN fun b hb =>
      odd_normalizer_inner_of_isFundamentalOver_general hK.1 (hBN hb)
          (Odd.of_dvd_nat hBo (Subgroup.orderOf_dvd_natCard B hb))
  exact funSplit_of_le_sup_centralizer hK hBc hBo hB3 P.isPGroup' hperm hBK

end CFSG.LocalAnalysis.UniquenessCase.UC22
