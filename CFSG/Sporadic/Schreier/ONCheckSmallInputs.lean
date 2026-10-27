module

public import CFSG.Sporadic.Schreier.ONOuterData
public import Certificates.Data.CFSGNative.ONSchreier.Compact
public meta import CFSG.Sporadic.Schreier.ONOuterData
public meta import Certificates.Data.CFSGNative.ONSchreier.Compact
public meta import Mathlib.Init
public import Mathlib.Init

public section

namespace CFSG.ONSchreier

open CFSG.ONSchreier.Native

@[expose] def smallChainOK (n : Nat) (ch : Data.SmallChain) : Bool :=
  ch.degree == n && decide (ch.generators.size ≤ ch.strongGenerators.size) &&
    allBelowN ch.generators.size (fun j => peq n ch.generators[j]! ch.strongGenerators[j]! &&
      pisInv n ch.generators[j]! (pinvCand n ch.generators[j]!)) &&
    fullChainOK n ch.generators.size ch.strongGenerators ch.base
      (Array.replicate ch.generators.size [] ++ ch.derivations) 2

end CFSG.ONSchreier
