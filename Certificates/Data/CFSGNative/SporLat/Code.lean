module

public import Certificates.Data.CFSGNative.SporLat.Spec

public section

namespace CFSG.QuasithinUnique.Ch1.SporLat

@[expose] def encodeSet (n : Nat) (l : List Nat) : Nat :=
  l.foldr (fun p acc => (p + 1) + (n + 1) * acc) 0

@[expose] def decodeSet (n : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, c => if c = 0 then [] else (c % (n + 1) - 1) :: decodeSet n fuel (c / (n + 1))

@[expose] def codeAct (n : Nat) (t : Array Nat) (c : Nat) : Nat :=
  encodeSet n (sortN ((decodeSet n c c).map fun p => t.getD p 0))

@[expose] def codeSetAct (n : Nat) (t : Array Nat) (L : List Nat) : List Nat :=
  sortN (L.map (codeAct n t))

end CFSG.QuasithinUnique.Ch1.SporLat
