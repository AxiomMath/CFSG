
module

public import CFSG.Sporadic.Co1Block.ConjBData
public import CFSG.Sporadic.Co1Block.TwoBCheckBase
public import CFSG.Sporadic.Co1.Module.InvDataBase
public meta import CFSG.Sporadic.Co1Block.ConjBData
public meta import CFSG.Sporadic.Co1Block.TwoBData
public meta import CFSG.Sporadic.Co1Block.TwoBCheckDefs
public meta import CFSG.Sporadic.Co1.Module.InvDataBase
public meta import CFSG.Sporadic.Co1.Module.FormsBase
public meta import CFSG.Sporadic.Co1.Module.OrbitsBase
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.Co1.Involutions
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain

public section

namespace CFSG.Sporadic.Co1Block

open CFSG.Sporadic.Co1Schreier.Native CFSG.Monster.B.Co2.Native

@[noinline, expose] def conjBCheckOf (base : List Rows) (W : List (List Int)) (sB : Rows) :
    Bool :=
  let D := dag base W
  D.2.2 && mul (D.1.getD 10 one) (base.getD 0 one) == mul sB (D.1.getD 10 one)

@[expose] def inTriN (p : Nat × Nat) (x : Nat) : Bool :=
  x == p.1 || x == p.2 || x == (p.1 ^^^ p.2)

@[noinline, expose] def tabSoundOf (tab : Array Nat) (T : Array (Nat × Nat)) : Bool :=
  allLt (2 ^ 24) fun x => decide (1365 ≤ tab[x]!) || inTriN T[tab[x]!]! x

end CFSG.Sporadic.Co1Block
