module

public import CFSG.Sporadic.HNSchreier.OrbitCheck
public import Certificates.Data.CFSGNative.ONSchreier.Vectors
public meta import CFSG.Sporadic.HNSchreier.OrbitCheck
public meta import Certificates.Data.CFSGNative.ONSchreier.Vectors
public import CFSG.Sporadic.HNSchreier.ChainCheckInputs
public import Certificates.Certificate2096

public section

namespace CFSG.Sporadic.HNSchreier.Native

open CFSG.ONSchreier.Native CFSG.Sporadic.F5.Native

theorem card_J_cert :
    Nat.card (CFSG.Sporadic.F5.J hnsData) = 273030912000000 :=
  Certificates.certificate2096

@[irreducible, expose] def hnStrongArrs : Array (Array Nat) := strongOf (hnsData.orbit ())

theorem hnStrongArrs_eq : hnStrongArrs = strongOf (hnsData.orbit ()) := by
  unfold hnStrongArrs; rfl

end CFSG.Sporadic.HNSchreier.Native
