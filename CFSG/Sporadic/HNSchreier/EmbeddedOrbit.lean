module

public import CFSG.Sporadic.HNSchreier.PackedOrbitData
public meta import CFSG.Sporadic.HNSchreier.IncludeOrbit
public import CFSG.Sporadic.HNSchreier.IncludeOrbit

public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
set_option compiler.extract_closed false

namespace CFSG.Sporadic.HNSchreier.Native

@[expose] def hnsOrbitData (_ : Unit := ()) : PackedOrbitData := hn_orbit_data% 1140000

@[expose] def hnsOrbit (_ : Unit := ()) : CFSG.Sporadic.F5.Native.VOrbit :=
  (hnsOrbitData ()).toOrbit

end CFSG.Sporadic.HNSchreier.Native
