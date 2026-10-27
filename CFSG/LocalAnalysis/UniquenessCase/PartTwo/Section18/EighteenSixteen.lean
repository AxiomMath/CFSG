module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSixteenCaseTwo
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusLineStab

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

section Certified


theorem eighteen_sixteen_two (D : Data G) (h61 : UC6.R6_1 D)
    (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) (h1742 : S17.R17_42At D V₀ V)
    (h142 : R18_14_2At D V₀ V p L h) :
    R18_16_2At D V₀ V p L h := by
  have hKl : K_Omega6Minus_lineStab := k_K_Omega6Minus_lineStab_holds
  intro s hP
  have hP' := hP
  obtain ⟨hs1, hs2, -⟩ := hP
  interval_cases s
  · exact eighteen_sixteen_two_s1 D V₀ V p L h h61 h1742 h142 hKl hP'
  · exact eighteen_sixteen_two_s2 D V₀ V p L h h61 h1742 h142 hKl hP'

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
