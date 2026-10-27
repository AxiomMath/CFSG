module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102KFacts
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102TorusFixU4
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102TorusFixU5

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

theorem kU45TorusFix_holds : KU45TorusFix := by
  intro X _ _ n hX S hS hSi Θ hΘ hΘS
  rcases hX with ⟨hU5, rfl⟩ | ⟨hU4, hn⟩
  · exact torusFixConcl_of_lieModel_PSU_five hU5 S hS hSi Θ hΘ hΘS
  · obtain ⟨K, _, h, ⟨e⟩⟩ := CFSG.Quasithin.H13.U4Par.exists_hypSU_equiv_of_lieModel hU4
    exact (torusFixConcl_hypSU_two_zero h hn).of_mulEquiv e.symm S hS hSi Θ hΘ hΘS

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

end
