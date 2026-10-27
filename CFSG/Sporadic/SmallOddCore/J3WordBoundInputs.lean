module

public import CFSG.Sporadic.SmallOddCore.J3
public import CFSG.Sporadic.SmallOddCore.AutCount
public import CFSG.Sporadic.Schreier.PairJ3Pairs
public meta import CFSG.Sporadic.Schreier.PairJ3Check
public meta import Certificates.Data.CFSGNative.PairSchreier.Preds
public import Certificates.Certificate2236
public import Certificates.Certificate2237
public import Certificates.Certificate2238
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CFSG.Sporadic.SmallOddCore

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

@[expose] def j3WPat : List Bool := [false, true, false, true, false, true, true]

@[expose] def j3WConds : List (List Bool × ℕ) :=
  [([false, true], 19), ([false, true, false, true, true], 9), (j3WPat, 17)]

end CFSG.Sporadic.SmallOddCore
