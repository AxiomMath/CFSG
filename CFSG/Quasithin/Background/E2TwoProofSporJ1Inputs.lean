module

public import Certificates.Data.CFSGNative.J1.Certificate
public import Certificates.Data.CFSGNative.Th.Tables
public import Certificates.Data.CFSGNative.SporLat.Build
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBaseNative

public section

namespace CFSG.Quasithin.E2P.SporB.J1Lat

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.Sporadic.Th.Native

@[expose] def j1ta : List Nat :=
  (List.range 1540).map (ap (CFSG.Sporadic.J1.Native.orbitData ()).alpha)

@[expose] def j1tb : List Nat :=
  (List.range 1540).map (ap (CFSG.Sporadic.J1.Native.orbitData ()).beta)

@[expose] def j1Words : List (List Nat) :=
  [[0],
    [1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0,
      1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1],
    [1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1,
      0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1]]

@[expose] def j1STabs : List (Array Nat) :=
  j1Words.map (wordTabA #[j1ta.toArray, j1tb.toArray] 1540)

@[expose] def j1Delta : List Nat := [27, 623, 1344, 1386]

@[expose] def j1Lat : LatData (List Nat) :=
  buildLat ptAct 1540 j1ta.toArray j1tb.toArray j1Delta j1STabs 400

@[expose] def j1Enum : Array (List Nat) × Array Nat × Array Nat :=
  bfsEnumB 1540 (List.range 1540) j1STabs j1STabs 100

end CFSG.Quasithin.E2P.SporB.J1Lat
