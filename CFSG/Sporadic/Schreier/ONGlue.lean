module

public import Certificates.Data.CFSGNative.ONSchreier.Compact

public section

namespace CFSG.ONSchreier.Native

@[expose] def restrictOK (g R t : Array Nat) : Bool :=
  allBelowN R.size fun k => decide (t[k]! < R.size) && R[t[k]!]! == g[R[k]!]!

@[expose] def inBlock (b : Array Nat) (y : Nat) : Bool := b[0]! == y || b[1]! == y

@[expose] def blockImgOK (g : Array Nat) (B : Array (Array Nat)) (t : Array Nat) : Bool :=
  allBelowN B.size fun i => decide (t[i]! < B.size) &&
    inBlock B[t[i]!]! g[(B[i]!)[0]!]! && inBlock B[t[i]!]! g[(B[i]!)[1]!]!

@[expose] def coversOK (n : Nat) (A B : Array (Array Nat)) : Bool :=
  allBelowN A.size fun i => peq n A[i]! (pid n) || !(allBelowN B.size fun j => !peq n A[i]! B[j]!)

@[expose] def countBelowN (m : Nat) (p : Nat → Bool) : Nat := ((List.range m).filter p).length

@[expose] def sortedOK (b : Array Nat) : Bool :=
  allBelowN b.size fun k => k + 1 == b.size || decide (b[k]! < b[k + 1]!)

end CFSG.ONSchreier.Native
