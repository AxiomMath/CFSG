module

public import Certificates.Data.CFSGNative.Co1.S365CentWit
public import CFSG.Monster.GMS.S365CosetInputs
public import CFSG.Monster.GMS.S365RootInputs

@[expose] public section

namespace CFSG.Monster.GMS.S365

open CFSG.Blueprint.NativeSporadic
open scoped Matrix
open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.Module
  CFSG.Sporadic.Co1.Module.Pairs CFSG.Sporadic.Co1.S365Native CFSG.Sporadic.Co1.InvNative
  CFSG.Sporadic.Co1.S365CentNative

def wordA : List ℕ :=
  [2, 2, 0, 0, 2, 2, 2, 0, 0, 0, 2, 2, 0, 2, 2, 0, 2, 0, 0, 0, 2, 0, 0, 1, 2, 0, 2, 0, 0, 2, 2, 2,
    0, 0, 2, 0, 0, 2, 0, 0, 2]

def wordB : List ℕ :=
  [2, 2, 2, 2, 2, 2, 0, 2, 2, 0, 2, 0, 0, 0, 0, 2, 2, 0, 2, 1, 2, 0, 0, 2, 0, 2, 0, 2, 0, 2, 2, 2,
    2, 2, 0, 2, 0, 2, 2, 2, 2, 2]

def witCheckRef : Bool :=
  witCheck qRows (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 2 4 40
    cosetRowsT wordA wordB

def noPatRef : Bool :=
  noPat qRows (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 rootGs

end CFSG.Monster.GMS.S365
