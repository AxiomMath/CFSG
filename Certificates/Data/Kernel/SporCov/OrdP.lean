module

public import Certificates.Data.Kernel.SporCov.LaneKit
public import CFSG.Certificates.Kernel.Orders.Cert

public section

namespace CFSG.KC.SporCov

@[expose] noncomputable def ordPK (mul : Nat → Nat → Nat) (ONE Y p : Nat) : Bool :=
  forceR Y fun y => CFSG.KC.Ord.andB (Nat.beq (CFSG.KC.Ord.powR mul ONE y p) ONE)
    (CFSG.KC.Ord.notB (Nat.beq y ONE))

@[expose] def invL (c : Nat) : Nat := if c % 2 = 0 then c + 1 else c - 1

@[expose] def invK (u : List Nat) : List Nat := (u.map invL).reverse

@[expose] def cjK (g x : List Nat) : List Nat := invK g ++ (x ++ g)

end CFSG.KC.SporCov

end
