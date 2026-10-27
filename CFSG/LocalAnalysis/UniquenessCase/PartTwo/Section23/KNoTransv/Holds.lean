module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsTwoThree
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNoTransv.Transvection
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNoTransv.XCases
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNoTransv.CaseSimple
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNoTransv.CaseProd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open NoTransv

theorem kNoTransv_holds : KNoTransv := by
  intro B _ _ hB H X _ _ k s hX hk hH ⟨f, hf, hker⟩ hsN hs2 hsH
  by_contra hlt
  have hs1 : s ≠ 1 := by
    rintro rfl
    simp at hs2
  have hs := isTransvection_of_rkIdx_lt hB hs1 (by omega)
  rcases xCases hX hk with ⟨hS, hord⟩ | ⟨S₀, _, hS₀, hord, ⟨e⟩⟩
  · exact not_isTransvection_of_simple hB hH hord f hf hker hsN hsH hs
  · refine not_isTransvection_of_prod hB hH hord (e.toMonoidHom.comp f) (e.surjective.comp hf) ?_
      hsN hsH hs
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    simpa using hx

end CFSG.LocalAnalysis.UniquenessCase.UC22
