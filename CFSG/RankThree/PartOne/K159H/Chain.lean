module

public import CFSG.RankThree.PartOne.KFCL.GenDefs
public import CFSG.RankThree.PartOne.K159.InnLayerRows
public import CFSG.RankThree.PartOne.K159.ThetaChain
public import CFSG.RankThree.PartOne.S13K.KFLiftRows

public section

namespace CFSG.RankThree.PartOne.K159

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S15K
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem kfCompLayer_of_gen (hS : SchreierFor InCatalog)
    (h82 : LocalThetaComponentEmbeddingFrontier) (hS13 : Sec13Avail) (hAt : KFCL.KFAtEven)
    (hGen : KFCL.KFCompGenEven) : KFCompLayer := by
  intro G _ _ p A c L E h15 hF hout hEA e he he1 Q hQle hQc
  have hnot5 : ¬ Outcome152Five p E A (lieGenerated p E) := by
    subst hEA
    rintro ⟨-, -, -, -, -, -, hne, -⟩
    exact hne rfl
  obtain ⟨r, hr1, hr4, hrow⟩ := KFCL.outcome152_cases hout hnot5
  have h13 : Sec13Facts G p A c L E := hS13 G p A c L E h15.h12 hnot5
  refine (hGen r hr1 hr4 G p A c L E h15 hF h13 hrow e he he1 Q hQle hQc).trans
    ((Subgroup.closure_le _).2 ?_)
  rintro x ⟨t, ht, hfix, K, hK, hxK⟩
  obtain ⟨g, hAtt⟩ := hAt r hr1 hr4 G p A c L E h15 hF h13 hrow t ht
  have hq : CFSG.IsQuasisimple ↥(kZero p E t) := S13K.isQuasisimple_of_model_psl_two hAtt.2.1
  exact isKt_le_thetaLayer hS h82 h15.h12 hK hq hfix he1 hxK

end CFSG.RankThree.PartOne.K159
