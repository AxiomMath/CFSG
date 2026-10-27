
module

public import CFSG.RankThree.Native.LyOperatorData
public meta import Certificates.Data.CFSGNative.Ly.Certificate
public import CFSG.Certificates.CyclicIntertwiner
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.FiveFacts
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.Ly.PrimitiveBase
public import CFSG.Sporadic.Ly.WordFacts
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.Schreier.LyChain11
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Sporadic.Th.OrbitSpec
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.RankThree.Native

open CFSG.Sporadic.He.Native CFSG.Sporadic.Ly.Native

@[expose] def lyNeId (X : Array (Array ℕ)) : Bool :=
  (List.range 111).any fun i => (List.range 111).any fun j =>
    (X[i]!)[j]! % 5 != (if i = j then 1 else 0)

@[expose] def lyZeroM : Array (Array ℕ) := Array.replicate 111 (Array.replicate 111 0)

@[expose] def lyEArr : Array (Array ℕ) := mulM 5 111 (keyTensor rootKey) formF

@[expose] def lyAB : Array (Array ℕ) := mulM 5 111 matA matB

@[expose] def lyCheckAB14 : Bool := powM 5 111 lyAB 14 == idM 111

@[expose] def lyCheckAB7 : Bool := lyNeId (powM 5 111 lyAB 7)

@[expose] def lyCheckAB2 : Bool := lyNeId (powM 5 111 lyAB 2)

@[expose] def lyCheckA : Bool := lyNeId matA

@[expose] def lyCheckB : Bool := lyNeId matB

@[expose] def lyCheckX : Bool := lyNeId matX

@[expose] def lyCheckFsymm : Bool := transM formF == formF

@[expose] def lyCheckFinv : Bool := mulM 5 111 formF (invM 5 111 formF) == idM 111

@[expose] def lyCheckS : Bool :=
  (List.range 7).all fun a => (List.range 7).all fun b =>
    (keyS rootKey)[7 * a + b]! == (keyS rootKey)[7 * b + a]!

@[expose] def lyCheckE : Bool := mulM 5 111 lyEArr lyEArr == lyZeroM

@[expose] def lySeedChecks : Bool :=
  lyCheckAB14 && lyCheckAB7 && lyCheckAB2 && lyCheckA && lyCheckB && lyCheckX && lyCheckFsymm &&
    lyCheckFinv && lyCheckS && lyCheckE

end CFSG.RankThree.Native
