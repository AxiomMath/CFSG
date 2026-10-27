module

public import CFSG.Sporadic.Co1Patterson.GraphRonanInputs

public section

namespace CFSG.Sporadic.Co1Patterson.Native

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Block

@[expose] def wRows (i : Nat) : Rows := vtxR (wP i).1 (wP i).2

@[expose] def amalgamCheck : Bool :=
  orbE.c.pts[triRoots.getD 2 0]! == mul iotaARows (repRows 1) &&
    decide (1 ≤ gensKe.getD 4 0) && decide (gensKe.getD 4 0 ≤ 190) &&
    mul (mul (gEl (gensKe.getD 4 0)) (wRows (triW.getD 2 0))) (gElInv (gensKe.getD 4 0)) ==
      wRows (triW.getD 0 0)

end CFSG.Sporadic.Co1Patterson.Native
