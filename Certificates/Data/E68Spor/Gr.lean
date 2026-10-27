module

public import Certificates.Data.CFSGNative.SporLat.Spec

public section

namespace CFSG.Quasithin.E6.Spor

open CFSG.QuasithinUnique.Ch1.SporLat

@[expose] def grAct (n : Nat) (t : Array Nat) (L : List Nat) : List Nat :=
  sortN (L.map fun c => t.getD (c / n) 0 * n + t.getD (c % n) 0)

@[expose] def grLabel (n : Nat) (z : Array Nat) : List Nat :=
  (List.range n).map fun p => p * n + z.getD p 0

end CFSG.Quasithin.E6.Spor
