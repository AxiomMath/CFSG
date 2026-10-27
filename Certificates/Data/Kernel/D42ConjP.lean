module

public import Certificates.Data.Kernel.D4PlaneP

public section

namespace CFSG.KC.D42ConjP

open CFSG.KC.D4PlaneP

@[expose] def isKP (kA kB y : Nat) : Bool := y == kA || y == kB

@[expose] def hitP (kA kB a b x : Nat) : Bool := isKP kA kB (mulP (mulP a x) b)

@[expose] def hitW (ls : List Nat) (kA kB x : Nat) (w : List Nat) : Bool :=
  hitP kA kB (wordP ls w) (wordP ls w.reverse) x

@[expose] def conjAnyP (ls : List Nat) (kA kB : Nat) (ws : List (List Nat)) (x : Nat) : Bool :=
  x == oneP || !cube1P x || ws.any fun w => hitW ls kA kB x w

@[expose] def conjIxP (ls : List Nat) (kA kB : Nat) (ws : List (List Nat)) (x i : Nat) : Bool :=
  x == oneP || !cube1P x || (decide (i < ws.length) && hitW ls kA kB x (ws.getD i []))

@[expose] def ixAllP (ls : List Nat) (kA kB : Nat) (ws : List (List Nat)) :
    List Nat → List Nat → Bool
  | [], [] => true
  | x :: xs, i :: is => conjIxP ls kA kB ws x i && ixAllP ls kA kB ws xs is
  | _, _ => false

end CFSG.KC.D42ConjP

end
