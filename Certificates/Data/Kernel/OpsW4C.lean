module

public import Certificates.Data.Kernel.OpsRenL

public section

namespace CFSG.KC.OpsW4N

open CFSG.KC.LQT CFSG.KC.OpsLayK

@[expose] noncomputable def w4FinL (c : Lay) (xs : List Nat) (T : Nat) (tests : List Nat) : Bool :=
  elemK c xs tests && Nat.beq (c.mul T T) c.ONE &&
    tests.any (fun k => !Nat.beq (c.vec (c.unit k) T) (c.unit k)) &&
    xs.all (fun X => commK c X T)

end CFSG.KC.OpsW4N

end
