
module

public import CFSG.Monster.GMS.S365CosetInputs
public import CFSG.Sporadic.Co1.Module.PairsCheckInputs

@[expose] public section

namespace CFSG.Monster.GMS.S365

open CFSG.Blueprint.NativeSporadic
open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.Module
  CFSG.Sporadic.Co1.Module.Pairs CFSG.Sporadic.Co1.S365Native CFSG.Sporadic.Co1.InvNative

def orbitCheck3Of (T : Array ℕ × Array ℕ × Array ℕ) : Bool :=
  treeCheckK cosetRowsT 0 0 T.1 T.2.1 T.2.2 && T.1[0]! == 28 && decide (397 ≤ T.1.size) &&
    T.1.all (fun v => decide (v < 2 ^ 24)) && decide T.1.toList.Nodup

def orbitCheck3 : Bool := orbitCheck3Of (cosetBFS cosetRowsT 0 0 28 400)

end CFSG.Monster.GMS.S365
