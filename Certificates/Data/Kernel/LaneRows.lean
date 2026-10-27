module

public import Certificates.Data.Kernel.LocalQT.Sec
public import Certificates.Data.Kernel.Misc.Coset.Mat

public section

namespace CFSG.KC.LaneRows

open CFSG.KC.LQT CFSG.KC.MiscCoset.Mat

@[expose] noncomputable def rowsEqK (c : Lay) (A : Nat) (X : List (List Nat)) : Bool :=
  (List.range c.d).all fun i => (List.range c.d).all fun j =>
    Nat.beq (A / 2 ^ (c.S * i + c.w * j) % 2 ^ c.w % c.p) (nthN (nthR X i) j % c.p)

end CFSG.KC.LaneRows

end
