module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicJ2Inputs
public import Certificates.Data.CFSGNative.SporLat.Build
public import Certificates.Data.CFSGNative.SporLat.Code
public import CFSG.Foundations
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.QuasithinUnique.K1.Interface
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRep
public import CFSG.Sporadic.Bridge.J2
public import CFSG.Sporadic.J2.Simple
public import CFSG.Sporadic.Th.F2Spec
public import Certificates.Certificate113

public section

namespace CFSG.Quasithin.E2P.SporB.J2Lat

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm

@[expose] def j2Sets : List (List ℕ) :=
  [[16, 28], [16, 147], [28, 155], [70, 244], [70, 280], [77, 244], [77, 280], [147, 155]]

@[expose] def j2Delta : List ℕ := sortN (j2Sets.map (encodeSet 315))

@[expose] def j2STabs : List (Array ℕ) := j2Qp.map fun p => j2SLP[p.1]!

@[expose] def j2Lat : LatData (List ℕ) :=
  buildLat (codeSetAct 315) 315 j2ta.toArray j2tb.toArray j2Delta j2STabs 400

end CFSG.Quasithin.E2P.SporB.J2Lat
