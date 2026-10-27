module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22tha
public import CFSG.Quasithin.Background.A3FactsTrialityTwo
public import CFSG.RankThree.PartOne.TCB.Final
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs13

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LocalAnalysis.UniquenessCase.UC22

theorem thinList13_of_bridge
    (hB : CFSG.RankThree.PartOne.TauCetiCatalogBridge) : ThinList13 := by
  intro X _ _ hK hq hO2 hrank
  have hrank' : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.Open.pRank r (⊤ : Subgroup X) ≤ 1 := fun r hr hr2 => by
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact hrank r hr hr2
  have hZ := uc22p22th_center_eq_bot hq.1 hO2 hrank'
  obtain ⟨hsimple, hnonab⟩ := uc22p22th_simple hq hZ
  haveI := hsimple
  have hSQT : CFSG.IsStronglyQuasithin X := fun p hp hp2 => (hrank p hp hp2).trans (by norm_num)
  have hcat := uc22p22th_catalog hnonab hK hB
  have hlist := CFSG.Milestones.cl_lit_sqtk_simple_list X hnonab hSQT hcat
  have h134 := CFSG.Quasithin.A3Facts.rankOneList X hsimple hnonab hlist hrank'
  exact ⟨hsimple, uc22p22th_of_a134 hrank' h134⟩

theorem thinList13_holds :
    ThinList13 :=
  thinList13_of_bridge CFSG.RankThree.PartOne.TCB.tauCetiCatalogBridge

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
