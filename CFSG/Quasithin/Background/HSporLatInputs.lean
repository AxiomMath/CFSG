module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicMathieuInputs
public import Certificates.Data.CFSGNative.SporLat.Build
public import Certificates.Data.CFSGNative.SporLat.Code
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Schreier.M23

public section

namespace CFSG.Quasithin.H.MathieuLat

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm

@[expose] def m12Sets : List (List ℕ) := [[0, 3, 4, 6, 7, 8, 10, 11], [1, 2, 5, 9], [1, 9], [2, 5]]

@[expose] def m12Delta : List ℕ := sortN (m12Sets.map (encodeSet 12))

@[expose] def m12STabs : List (Array ℕ) := m12Qp.map fun p => m12SLP[p.1]!

@[expose] def m12Lat : LatData (List ℕ) :=
  buildLat (codeSetAct 12) 12 m12ta.toArray m12tb.toArray m12Delta m12STabs 20

@[expose] def m22Sets : List (List ℕ) :=
  [[0, 1, 2, 4, 5, 6, 7, 8, 9, 12, 14, 15, 16, 17, 19, 21], [3, 10, 11, 20], [3, 11], [10, 20],
    [13, 18]]

@[expose] def m22Delta : List ℕ := sortN (m22Sets.map (encodeSet 22))

@[expose] def m22STabs : List (Array ℕ) := m22Qp.map fun p => m22SLP[p.1]!

@[expose] def m22Lat : LatData (List ℕ) :=
  buildLat (codeSetAct 22) 22 m22ta.toArray m22tb.toArray m22Delta m22STabs 100

@[expose] def m23Sets : List (List ℕ) :=
  [[0, 5, 9, 16], [0, 16], [1, 2, 3, 6, 7, 8, 10, 11, 12, 13, 14, 17, 19, 20, 21, 22], [5, 9],
    [15, 18]]

@[expose] def m23Delta : List ℕ := sortN (m23Sets.map (encodeSet 23))

@[expose] def m23STabs : List (Array ℕ) := m23Qp.map fun p => m23SLP[p.1]!

@[expose] def m23Lat : LatData (List ℕ) :=
  buildLat (codeSetAct 23) 23 m23ta.toArray m23tb.toArray m23Delta m23STabs 4000

end CFSG.Quasithin.H.MathieuLat
