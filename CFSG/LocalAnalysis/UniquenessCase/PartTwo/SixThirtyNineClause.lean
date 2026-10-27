module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixThirtyNine
public import CFSG.Yardstones.Me2c15c2c995a.Definitions
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem r6_39_of_gf2nCatalogClause (D : Data G)
    (h05 : CFSG.Yardstones.Me2c15c2c995a.GF2nCatalogClause)
    (hcat : ¬ CFSG.Blueprint.Catalog G) : R6_39 D := by
  intro V hV hTI
  have := D.standing.simple
  obtain ⟨hK, hchar, hM, hmax⟩ := gf2nTypeHyps_of_inCalVStar D hV
  exact hcat (h05 G D.standing.nonab hK hchar D.M hM V hmax hTI)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
