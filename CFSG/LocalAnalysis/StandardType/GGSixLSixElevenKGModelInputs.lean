module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExcHardF4
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExcHardE6
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExcHardE7
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExcHardE8
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExcHardTwE6
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutOutdiagE6Glue
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutOutdiagTwE6Glue

public section

namespace CFSG.StandardType

section

@[expose] def GGSixLSixElevenKGModelInputs : Prop :=
  GGOrdPToralF4RestHard ∧ GGOrdPToralE6RestHard ∧ GGOrdPToralE7RestHard ∧
    GGOrdPToralE8RestHard ∧ GGOrdPToralTwE6RestHard ∧
    GGE6NontoralFixPpdInput ∧ GGE6ToralFixNoPpdInput ∧
    GGTwE6FrameNoPpdInput ∧ GGTwE6FrameFixPpdInput

end

end CFSG.StandardType
