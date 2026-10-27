module

public import CFSG.Certificates.Kernel.Enum.Defs
public import Certificates.Data.Kernel.Spor.Chain
public import Certificates.Data.CFSGNative.Th.Tables

public section

namespace CFSG.KC.YoshQ

open CFSG.KC.Enum CFSG.KS CFSG.Sporadic.Th.Native

@[expose] noncomputable def tabN (n w x : Nat) : Table :=
  Array.ofFn (n := n) fun i => UInt32.ofNat (pg w (mask w) (x % 2 ^ (n * w)) i.val)

@[expose] noncomputable def pmN (n w x y : Nat) : Nat := pcomp n w (mask w) (x % 2 ^ (n * w)) y

@[expose] noncomputable def eqN (n w x y : Nat) : Bool :=
  Nat.beq (x % 2 ^ (n * w)) (y % 2 ^ (n * w))

@[expose] noncomputable def setF (w acc v i : Nat) : Nat :=
  acc ^^^ ((pg w (mask w) acc v ^^^ i) <<< (w * v))

@[expose] noncomputable def invN (n w x : Nat) : Nat :=
  (List.range n).foldl (fun acc i =>
    if pg w (mask w) (x % 2 ^ (n * w)) i < n then
      setF w acc (pg w (mask w) (x % 2 ^ (n * w)) i) i
    else acc) 0

end CFSG.KC.YoshQ

end
