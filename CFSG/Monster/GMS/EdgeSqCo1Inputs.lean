module

public import Certificates.Data.CFSGNative.Co1.EdgeSq
public import CFSG.Sporadic.Co1.Module.PairsCheckInputs

@[expose] public section

namespace CFSG.Monster.GMS.EdgeSq

open CFSG.Blueprint.NativeSporadic
open scoped Matrix
open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.Module
  CFSG.Sporadic.Co1.Module.Pairs CFSG.Sporadic.Co1.EdgeSqNative CFSG.Sporadic.Co1.S365UNative
  CFSG.Sporadic.Co1.InvNative CFSG.Sporadic.Co1.S365Native

def edgeCheck (S : Array ℕ) : Bool :=
  edgeCheckN qRows (transposeRows 24 f0Rows) (orbitOf 2 98280).pts
    (posTable 24 (orbitOf 2 98280).pts) 98280 S

end CFSG.Monster.GMS.EdgeSq
