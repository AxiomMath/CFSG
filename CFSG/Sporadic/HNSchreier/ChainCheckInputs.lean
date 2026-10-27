module

public import CFSG.Sporadic.HNSchreier.OrbitCheck
public import Certificates.Data.CFSGNative.ONSchreier.Vectors
public meta import CFSG.Sporadic.HNSchreier.OrbitCheck
public meta import Certificates.Data.CFSGNative.ONSchreier.Vectors

public section

namespace CFSG.Sporadic.HNSchreier.Native

open CFSG.ONSchreier.Native CFSG.Sporadic.F5.Native

@[expose] def strongOf (O : VOrbit) : Array (Array Nat) :=
  strongArrs hnsData.n (natTab O.alpha) (natTab O.beta) Data.strongWords

@[noinline, expose] def chainChecks (O : VOrbit) : Bool :=
  let S := strongOf O
  pointChainOK hnsData.n 2 S Data.baseList.toArray Data.strongWords 4 &&
    cOrbitSizes hnsData.n S Data.baseList.toArray == Data.schreierOrbitSizes && S.size == 9 &&
    peq hnsData.n S[0]! (natTab O.alpha) && peq hnsData.n S[1]! (natTab O.beta)

end CFSG.Sporadic.HNSchreier.Native
