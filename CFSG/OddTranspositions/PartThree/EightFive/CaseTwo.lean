module

public import CFSG.OddTranspositions.PartThree.EightFive.CaseTwoStatement

import CFSG.OddTranspositions.PartThree.EightFive.CaseTwoBlocks
import CFSG.OddTranspositions.PartThree.EightFive.CaseTwoThirdKind
import CFSG.OddTranspositions.PartThree.EightFive.CaseTwoCommute

public section

namespace CFSG.OddTranspositions.PartThree

section Certificates


theorem eightFiveCaseTwo_holds : EightFiveCaseTwo := by
  intro G _ _ D hC hrad _ _ w v htri hv n hn hn1 hord z hzdef htrans hB hQ hα
  obtain ⟨q, hq, c, htriqa, m, hm, -, hordqa⟩ :=
    exists_thirdKind_of_uQ_subset hC hrad htri hv hn hn1 hord hzdef htrans hQ hα
  have hc : c ∉ hC.alpha := not_mem_alpha_of_isTriangle hC
    (block_pairwise_commute_of_uQ_subset hC htri hv hn hord hzdef htrans hQ hα) htriqa
  exact exists_commute_of_thirdKind_conj_pCore_of_not_mem_alpha hC hrad htri hn hn1 hord hzdef
    htrans hB hα hq rfl htriqa hm hordqa rfl hc

end Certificates

end CFSG.OddTranspositions.PartThree
