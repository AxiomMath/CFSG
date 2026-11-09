module

public import Certificates.Data.Kernel.LocalQT.SecF3

public section

namespace CFSG.KC.LQT

open CFSG.KC.Ord CFSG.F3.Native CFSG.KS.F3L

@[expose] noncomputable def mulF3 (c : Lay) (K X A B : Nat) : Bool :=
  andB (Nat.beq c.p (nat_lit 3)) (andB (Nat.ble (Nat.mul c.d c.d) (Nat.shiftLeft (nat_lit 1) K))
    (andB (Nat.blt (nat_lit 0) c.d) (andB (validM c.p (Nat.mul c.d c.S) c.L c.H A)
      (andB (validM c.p (Nat.mul c.d c.S) c.L c.H B) (andB (validM c.p (Nat.mul c.d c.S) c.L c.H X)
        (eqV (gath3 c.w K X) (mulLane c.d (spreadE c.d c.d) (gath3 c.w K A) (gath3 c.w K B))))))))

end CFSG.KC.LQT

end
