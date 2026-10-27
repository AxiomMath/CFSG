module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102KFacts
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102U45KeyU4
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102U45KeyU5

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.ClassicalGroups.UnitaryFlag

theorem kU45Key_holds : KU45Key := by
  intro X _ _ n hX p hp hp2 hp3 hpn R hR
  rcases hX with ⟨hU5, rfl⟩ | ⟨hU4, hn⟩
  · have hp5 : p ≠ 5 := by
      rintro rfl
      exact hpn (by norm_num)
    exact u45KeyConcl_of_lieModel_PSU_five hU5 hp hp2 hp3 hp5 R hR
  · obtain ⟨K, _, h, ⟨e⟩⟩ := CFSG.Quasithin.H13.U4Par.exists_hypSU_equiv_of_lieModel hU4
    have hX' : UC22.IsU4 (hypSU h 2 0) n := CFSG.Blueprint.LieModel.of_mulEquiv e.symm hU4
    exact U45KeyConcl.of_mulEquiv e.symm
      (u45KeyConcl_hypSU_two_zero h hn hX' hp hp2 hp3 hpn) R hR

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

end
