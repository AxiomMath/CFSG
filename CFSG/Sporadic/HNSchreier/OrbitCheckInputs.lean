module

public import Certificates.Data.CFSGNative.HN.Data
public import CFSG.Sporadic.HNSchreier.Data
public import CFSG.Sporadic.HNSchreier.OrbitBuildInputs
public import CFSG.Sporadic.HNSchreier.EmbeddedOrbit
public meta import Certificates.Data.CFSGNative.HN.Data
public meta import CFSG.Sporadic.HNSchreier.Data

public section

set_option compiler.extract_closed false

namespace CFSG.Sporadic.HNSchreier.Native

open CFSG.Sporadic.F5.Native CFSG.Sporadic.Th.Native

@[expose] def hnsData : F5Data :=
  { hnsBFSData with suppliedOrbit := some (fun _ => hnsOrbit ()) }

theorem hnsData_orbit : hnsData.orbit () = hnsOrbit () := rfl

@[expose] def ordStepT (alpha beta : Table) (st : Bool × Nat) (i : Nat) : Bool × Nat :=
  let m₁ := max st.2 (ap alpha i + 1)
  (st.1 && decide (i < st.2) && decide (ap alpha i ≤ st.2) && decide (ap beta i ≤ m₁),
    max m₁ (ap beta i + 1))

@[expose] def bfsOrderOK (n : Nat) (alpha beta : Table) : Bool :=
  let st := (List.range n).foldl (ordStepT alpha beta) (true, 1)
  st.1 && st.2 == n

@[noinline, expose] def orbitCertChecks (O : VOrbit) : Bool :=
  matrixChecks hnsData && orbitChecks hnsData O 3 && bfsOrderOK hnsData.n O.alpha O.beta

end CFSG.Sporadic.HNSchreier.Native
