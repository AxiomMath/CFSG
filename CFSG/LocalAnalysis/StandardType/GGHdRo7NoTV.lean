module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CDefs
import CFSG.LocalAnalysis.StandardType.GGRCCaseIIBasic

public section

namespace CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem noTV_holds : NoTVLeaf := by
  intro G _ _ p _ Bs hNT V _ _ ι a ha hTv
  obtain ⟨ψ, hψ, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨g, hg, hgN, hgφ⟩ := mem_ggAutomizer_iff.mp hψ
  exact hNT ψ ⟨g, hg, hgN, hgφ⟩ (ggRC_isTransvection_of_lin ι ψ hTv)

end CFSG.StandardType.HdRo7C
