module

public import Certificates.Data.Kernel.Co1F2
public import Certificates.Data.CFSGNative.Co1.Odd

public section

namespace CFSG.KC.Co1Fix

open CFSG.KC.Co1F2 CFSG.KC.M1F2

@[expose] def spanK : List Nat → Nat → List Nat
  | [], a => [a]
  | f :: G, a => spanK G a ++ spanK G (a ^^^ f)

@[expose] noncomputable def fixListK (TA TB : Nat) (F W : List Nat) : Bool :=
  CFSG.Sporadic.Co1.OddNative.strictInc W &&
    W.all (fun x => decide (x < 2 ^ 24) && vmF 24 TA x == x && vmF 24 TB x == x) &&
    (spanK F 0).all fun y => !(vmF 24 TB y == y) || W.contains y

end CFSG.KC.Co1Fix

end
