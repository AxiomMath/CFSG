module

public import CFSG.LocalAnalysis.StandardType.GGTorusMaxAssembly
public import CFSG.LocalAnalysis.StandardType.GGTorusMaxOutProved
public import CFSG.LocalAnalysis.StandardType.GGTorusMaxSporadicOutProved

public section

namespace CFSG.StandardType.FrameRoute

theorem tmThreaded_lss92TorusMaxInput
    (hOver : LSS92MaxOvergroupInput) : LSS92TorusMaxInput :=
  tmAsm_lss92TorusMaxInput hOver tmLieOutAll_holds tmSporadicOutInput_proved
    CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
    CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds

end CFSG.StandardType.FrameRoute

end
