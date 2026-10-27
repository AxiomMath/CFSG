
module

public import CFSG.Sporadic.Schreier.ONCheckChainBase
public meta import CFSG.Sporadic.Schreier.ONCheckChainBase

public section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native

@[expose] def sigmaArr : Array Nat :=
  sigmaTab (vorbit (digitsW CFSG.ONSchreier.Data.rootDigits))
    (posOf (indexOf (vorbit (digitsW CFSG.ONSchreier.Data.rootDigits)).keys) nPts)

@[noinline, expose] def minusOK (S : Array (Array Nat)) (base sig : Array Nat) : Bool :=
  let invs := allInvSteps S (pinvs nPts S) base
  let Ls := cLevels nPts base (allSteps S (pinvs nPts S) base)
  let k0 := Ls[0]!.pos[sig[base[0]!]!]!
  let x1 := trInvApp invs[0]! Ls[0]! Ls[0]!.pts.size k0 sig[base[1]!]!
  let k1 := Ls[1]!.pos[x1]!
  let x2 := trInvApp invs[1]! Ls[1]! Ls[1]!.pts.size k1
    (trInvApp invs[0]! Ls[0]! Ls[0]!.pts.size k0 sig[base[2]!]!)
  pisInv nPts sig sig && decide (k0 < Ls[0]!.pts.size) && decide (k1 < Ls[1]!.pts.size) &&
    x2 == 81515 && !decide (Ls[2]!.pos[81515]! < Ls[2]!.pts.size) && base[2]! == 100817

end CFSG.Sporadic.ONOddCore
