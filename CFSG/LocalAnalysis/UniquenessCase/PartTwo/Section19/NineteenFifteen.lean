module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Statements

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem nineteen_fifteen (D : Data G) (h640 : UC6.R6_40_1 D)
    {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ}
    {Y N Dsub H S : Subgroup G}
    (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S) :
    R19_15At D V₀ V p L A t B r Y N Dsub H S h := by
  intro Lb
  exact h640 N h.hN.1.1 Lb

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
