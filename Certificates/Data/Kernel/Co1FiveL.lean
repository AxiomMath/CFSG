module

public import Certificates.Data.Kernel.Co1FiveK
public import Certificates.Data.Kernel.Co1F2

public section

namespace CFSG.KC.Co1FiveL

open CFSG.KC.Co1F2 CFSG.KC.Co1FiveK CFSG.KC.Co1B CFSG.KLie.CT

@[expose] noncomputable def betaK (AT : List Nat) (a b s : Nat) : Nat :=
  mulWK (pwK (getL (nat_lit 0) AT a) (Nat.div s (nat_lit 5)))
    (pwK (getL (nat_lit 0) AT b) (Nat.mod s (nat_lit 5)))

@[expose] noncomputable def btK (AT : List Nat) (a b : Nat) (BT : List Nat) : Bool :=
  andB (Nat.beq (lenL BT) (nat_lit 25))
    (allN (nat_lit 25) fun s => Nat.beq (getL (nat_lit 0) BT s) (trK (nat_lit 24) (betaK AT a b s)))

end CFSG.KC.Co1FiveL

end
