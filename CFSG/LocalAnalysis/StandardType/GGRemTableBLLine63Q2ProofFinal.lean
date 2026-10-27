module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63Q2ProofOne
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63Q2ProofTwo

public section

namespace CFSG.StandardType.Line63.H5

theorem line63Q2_holds :
    Line63Q2 :=
  line63Q2_of_steps line63StepOneQ2_holds line63StepTwoQ2_holds

theorem ggUnitDvd63BstarRankInput_holds :
    GGUnitDvd63BstarRankInput :=
  ggUnitDvd63BstarRankInput_of_q2 line63Q2_holds

end CFSG.StandardType.Line63.H5

end
