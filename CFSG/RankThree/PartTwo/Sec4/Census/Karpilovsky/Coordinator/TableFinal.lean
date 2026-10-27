module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TableFromLedger

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator


theorem sporadicMultipliers_of_openCells (h : SporadicOpenCells) : SporadicMultipliers :=
  sporadicMultipliers_of_ledger
    (fun s hs _ hp hp5 _ => Karpilovsky.Proving.kernelTrivialAt_carrier_of_five_le
      CFSG.RankThree.PartOne.MultRes.sporadicResidualKernelsTrim_holds s hs hp hp5) h

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
