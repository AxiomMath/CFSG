module

public import Certificates.Data.CFSGNative.Co1.S365CentRoot
public import CFSG.Monster.GMS.S365RootInputs

@[expose] public section

namespace CFSG.Monster.GMS.S365

open CFSG.Blueprint.NativeSporadic
open scoped Matrix
open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.Module
  CFSG.Sporadic.Co1.Module.Pairs CFSG.Sporadic.Co1.S365Native CFSG.Sporadic.Co1.InvNative
  CFSG.Sporadic.Co1.S365UNative CFSG.Sporadic.Co1.S365CentNative

def rootCount120 : Bool :=
  rootCountN qRows (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 rootGs
    (transposeRows 24 rowsSA) 120

def rootFixOK : Bool :=
  rootFix.all fun c => decide (c < 2 ^ 24) && isFixedN (transposeRows 24 rowsSA) c

end CFSG.Monster.GMS.S365
