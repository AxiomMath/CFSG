module

public import CFSG.Milestones.ASVolI.C1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.C127Holds

public section

namespace CFSG.ASVolI

section C127

set_option linter.unusedSectionVars false


theorem as_C_1_27
    : C_1_27 := by
  intro Ω _ _ X T H K hX hT hK hH hKb hKJ hHK
  obtain ⟨L, hL, hKL, -, hU, hcases⟩ :=
    CFSG.Quasithin.theoremC127_holds Ω X T H K hX hT hK hH hKb hKJ hHK
  exact ⟨L, hL, hKL, hU, hcases⟩

end C127

end CFSG.ASVolI
