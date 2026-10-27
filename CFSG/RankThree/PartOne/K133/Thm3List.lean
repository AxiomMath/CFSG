module

public import CFSG.RankThree.PartOne.S13K.KF133One
public import CFSG.RankThree.PartOne.N143.SectionListConsumers
import CFSG.RankThree.PartOne.S10.EmbeddingFixedResidual
public import CFSG.RankThree.PartOne.N143.Statements

public section

namespace CFSG.RankThree.PartOne.K133

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.N143

theorem kf133Thm3_of_list (h : SectionListBound) : KF133Thm3 := by
  intro G _ _ p A c L E hH hF hF13 hT t ht K hK e he he1 I hI hKI
  obtain ⟨hsimp, hnonab, hKP, -, he3, -⟩ := hH.setup
  have := hsimp
  have hItop : I ≠ ⊤ := by
    intro htop
    have hIC : I ≤ Subgroup.centralizer ({e} : Set G) := (mem_thetaComponentsAt_iff.1 hI).1
    exact EmbeddingFixedResidual.centralizer_ne_top_of_simple hnonab he1
      (eq_top_iff.2 (htop ▸ hIC))
  exact (theoremThreeListHyp_simpleQuot_of_mem_thetaComponentsAt h hKP he3.le hH.prime hI
    hItop).onList

end CFSG.RankThree.PartOne.K133
