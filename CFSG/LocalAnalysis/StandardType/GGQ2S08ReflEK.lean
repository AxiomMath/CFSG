module

public import CFSG.LocalAnalysis.StandardType.GGQTwoI1FailGlue
public import CFSG.LocalAnalysis.StandardType.GGQ2S08RestOut

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGQ2ReflEKOffI1Input : Prop :=
  GGQ2ReflEInput ∧ GGQ2ReflKInput

theorem ggQ2s08_reflE_of_ek (h : GGQ2ReflEKOffI1Input) : GGQ2ReflEInput :=
  h.1

theorem ggQ2s08_reflK_of_ek (h : GGQ2ReflEKOffI1Input) : GGQ2ReflKInput :=
  h.2

end CFSG.StandardType

end
