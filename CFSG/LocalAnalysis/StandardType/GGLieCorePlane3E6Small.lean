module

public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane3E6Label
public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane3A8Label

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.TableCRes

theorem ggLieSmallFormA8Plane3_E6 :
    GGLieSmallFormA8Plane3 .E6 := by
  intro L _ _ _ D ρ hρ hfin hq a₁ a₂ h₁ h₂ hp₁ hp₂ hcard i hR hA3
  obtain ⟨n, hn, hlab⟩ := ggLieFamLabel_E6 D ρ hρ hfin hq a₁ a₂ h₁ h₂ hp₁ hp₂ hcard i hR
  obtain ⟨f, hf, hqf⟩ := hq
  exact ggLieA8_of_label ρ hf hqf _ n hn _ hlab hA3

end CFSG.StandardType.LieCore
