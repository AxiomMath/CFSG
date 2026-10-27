
module

public import CFSG.Sporadic.HNOddCore.PCheckBase
public meta import CFSG.Sporadic.HNOddCore.PCheckBase

public section

namespace CFSG.Sporadic.HNOddCore.Native

open CFSG.ONSchreier.Native

@[noinline, expose] def witCoverChecks : Bool :=
  pReps.size == 29 && InvData.witRep.size == 39 && InvData.witKer.size == 39 &&
    InvData.nonRep.size == 9 &&
    (allBelowN 29 fun c => allBelowN 2 fun e =>
      InvData.nonRep.contains pReps[c]! || (pReps[c]! == 0 && e == 0) ||
        !(allBelowN 39 fun w => !(InvData.witRep[w]! == pReps[c]! && InvData.witKer[w]! == e))) &&
    (List.range 29).countP (fun c => InvData.nonRep.contains pReps[c]!) == 9 &&
    (allBelowN 39 fun w => pReps.contains InvData.witRep[w]! &&
      !InvData.nonRep.contains InvData.witRep[w]! && decide (InvData.witKer[w]! < 2) &&
      !(InvData.witRep[w]! == 0 && InvData.witKer[w]! == 0)) &&
    (allBelowN 39 fun w => allBelowN 39 fun w' => w == w' ||
      !(InvData.witRep[w]! == InvData.witRep[w']! && InvData.witKer[w]! == InvData.witKer[w']!))

end CFSG.Sporadic.HNOddCore.Native
