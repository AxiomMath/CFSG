module

public import Certificates.Data.Fi24Rank.KCheck
public import Certificates.Data.Fi22TwistCore
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi24TwoBK
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import Certificates.Kernel.Sporadic.Fi22.C2068
public import Certificates.Kernel.Sporadic.Fi22.C3151

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B.Fi24PlanesNative

open CFSG.Monster.B.Co2.Native CFSG.LocalAnalysis.GLTheoremA.H1017.Fi24RankNative
open CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime
open CFSG.LocalAnalysis.GLTheoremA.H1017.Fi22TwistNative (commAtN)

set_option compiler.extract_closed false

@[expose] def fi24PlRow (I : Array (Array Nat)) (t : Array Nat) : Array Bool :=
  I.map (commAtN 504 t)

@[noinline, expose] def fi24PlRows (P I : Array (Array Nat)) : Array (Array Bool) :=
  P.map (fi24PlRow I)

@[expose] def fi24PlCnt (r : Array Bool) : Nat := (List.finRange 243).countP fun i => r[i.val]!

@[expose] def fi24PlSame (P : Array (Array Nat)) (R : Array (Array Bool)) (e : Array Nat)
    (r : Array Bool) : Nat :=
  (List.finRange 4096).countP fun s =>
    eqA 504 P[s.val]! e || allLt 243 fun i => (R[s.val]!)[i]! == r[i]!

@[noinline, expose] def fi24PlCheck (P : Array (Array Nat)) (R : Array (Array Bool))
    (e : Array Nat) : Bool :=
  allLt 4096 fun t =>
    let c := fi24PlCnt R[t]!
    eqA 504 P[t]! e || decide (c < 81) || (c == 81 && decide (fi24PlSame P R e R[t]! ≤ 4))

@[expose] def fi24PlanesOK (_ : Unit := ()) : Bool :=
  let P := fi24NCert.pts
  fi24PlCheck P (fi24PlRows P (iotas 504 (kRA ()))) (idA 504)

end CFSG.LocalAnalysis.GLTheoremA.H301B.Fi24PlanesNative
