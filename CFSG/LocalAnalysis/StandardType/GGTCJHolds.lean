module

public import CFSG.LocalAnalysis.StandardType.GGTCJDatum
public import CFSG.LocalAnalysis.StandardType.GGTCJLabel
public import CFSG.LocalAnalysis.StandardType.GGTCJDivides

public section

namespace CFSG.StandardType.TCJ

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.Y10F CFSG.LocalAnalysis.GLTheoremA.Y10GField
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

theorem tcjSimple_holds :
    TCJSimple := by
  intro p hp hp2 S _ _ lab α K hlab hcen hin hα hK
  obtain ⟨labJ0, hJ0, hhas⟩ := tcj_component_hasLabel p hp hp2 lab α K hlab hcen hin hα hK
  rw [tcj_ggFixSub_eq_fixSubgroup] at hK
  have hdvd := tcj_inn_of_families_all S p α K lab labJ0 hp hp2 hcen hin hα hhas hK
  exact tcj_relabel hlab hJ0 hdvd (tcj_ggHasLabel_of_hasLabel hhas)

theorem ggTCJKnown_holds :
    GGTCJKnown :=
  ggTCJKnown_of_simple tcjSimple_holds

end CFSG.StandardType.TCJ

end
