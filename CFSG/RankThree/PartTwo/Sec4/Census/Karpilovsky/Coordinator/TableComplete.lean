module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TableFinal
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.KernelTrivialThreeFi23

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

theorem sporadicOpenCells_holds :
    SporadicOpenCells :=
  ⟨kernelTrivialAt_three_Fi23⟩


theorem sporadicMultipliers_holds : SporadicMultipliers :=
  sporadicMultipliers_of_openCells sporadicOpenCells_holds

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
