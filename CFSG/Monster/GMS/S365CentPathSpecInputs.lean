
module

public import Certificates.Data.CFSGNative.Co1.S365CentPath
public import CFSG.Monster.GMS.S365CosetInputs
public import CFSG.Sporadic.Co1.Module.PairsCheckInputs

@[expose] public section

namespace CFSG.Monster.GMS.S365

open CFSG.Blueprint.NativeSporadic
open scoped Matrix
open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.Module
  CFSG.Sporadic.Co1.Module.Pairs CFSG.Sporadic.Co1.S365Native CFSG.Sporadic.Co1.InvNative
  CFSG.Sporadic.Co1.S365CentNative

@[expose] def pathE1 : List ℕ := [0, 2, 2, 2, 0, 2, 2, 2, 2, 2, 0, 0, 2, 0, 2, 2, 0, 2, 2, 0, 2]

@[expose] def pathE2 : List ℕ := [2, 0, 2, 2, 0, 2, 0, 2, 0, 0, 2, 2, 0, 2, 0, 2, 0, 2]

@[expose] def pathE12 : List ℕ := [0, 0, 2, 2, 2, 2, 2, 0, 0, 2, 0, 2, 2, 0, 0, 0, 2, 0]

@[expose] def pathCheck : Bool :=
  applyPath cosetRowsT pathE1 cosetBase == (cosetBase ^^^ 2) &&
  applyPath cosetRowsT pathE2 cosetBase == (cosetBase ^^^ 4) &&
  applyPath cosetRowsT pathE12 cosetBase == (cosetBase ^^^ 2 ^^^ 4) &&
  cosetRowsT.all (fun Mt => isFixedN Mt 2 && isFixedN Mt 4) &&
  countBelow (pat4 qRows (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 2 4)
    16777216 0 == 1995840

end CFSG.Monster.GMS.S365
