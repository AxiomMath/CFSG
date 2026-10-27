module

public import Certificates.Data.CFSGNative.ONSchreier.Compact

public section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier.Native

@[expose] def dbl (n : Nat) (a b : Array Nat) : Array Nat := a ++ b.map (· + n)

@[expose] def dblBase (n : Nat) (base : Array Nat) : Array Nat := base ++ base.map (· + n)

@[expose] def posArr (n : Nat) (gs : Array (Array Nat)) (w : List Nat) : Array Nat :=
  w.foldr (fun l acc => pcomp n (gs.getD (l - 1) (pid n)) acc) (pid n)

@[expose] def posPt (gs : Array (Array Nat)) (w : List Nat) (p : Nat) : Nat :=
  w.foldr (fun l q => (gs.getD (l - 1) #[])[q]?.getD q) p

end CFSG.Sporadic.ONOddCore
