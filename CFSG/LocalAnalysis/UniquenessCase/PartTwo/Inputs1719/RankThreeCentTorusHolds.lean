module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.RankThreeCentTorusOmegaMinus8
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CartanTorusSp6
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CartanTorusU6
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Section17KFacts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

theorem k_RankThreeCentTorus_holds :
    K_RankThreeCentTorus := by
  intro K _ _ t m f p r hadm hL hq hZ hf ht hp hp2 hpd hr hr5 hrd
  simp only [CFSG.SectionRank.pRank_coe_eq_openPRank]
  rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [if_neg (by decide)]
    exact k_RankThreeCentTorus_u6 K f p r hadm hL hq hZ hp hp2 hpd hr hr5 hrd
  · rw [if_neg (by decide)]
    exact k_RankThreeCentTorus_omegaMinus8 K f p r hadm hL hq hZ hf hp hp2 hpd hr hr5 hrd
  · rw [if_pos rfl]
    exact k_RankThreeCentTorus_sp6 K f p r hadm hL hq hZ hf hp hp2 hpd hr hr5 hrd

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
