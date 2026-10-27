module

public import CFSG.Sporadic.SmallOddCore.IrrSylowCheck
public import CFSG.Sporadic.Schreier.ONOuterData
public meta import CFSG.Sporadic.SmallOddCore.IrrSylowCheck
public meta import CFSG.Sporadic.Schreier.ONOuterData
public meta import Mathlib.Init
public import Mathlib.Init

public section

namespace CFSG.Sporadic.SmallOddCore

open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native

@[expose] def onIrrSylowTbls : List Table :=
  (List.range 6).map fun j => CFSG.ONSchreier.Data.T32Chain.generators[j]!.map UInt32.ofNat

@[expose] def onIrrOK : Bool := irrSylowOK 32 600 512 onIrrSylowTbls (fun _ => true) []

end CFSG.Sporadic.SmallOddCore
