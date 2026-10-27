module

public import CFSG.Certificates.Kernel.Local.HN.X.Lib
public import CFSG.Certificates.Kernel.Enum.Defs
public import CFSG.Certificates.Kernel.Local.HN.Lib
public import CFSG.Certificates.Kernel.Local.LargeCore.Grp2

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KC.LL

@[expose] noncomputable def ckC (n k : Nat) : Nat :=
  nIf(Nat.ble (Nat.mul (nat_lit 32) (Nat.succ k)) n, nat_lit 32, Nat.sub n (Nat.mul (nat_lit 32) k))

@[expose] noncomputable def isIdK (X : Nat) : Bool :=
  allN (nat_lit 133) (fun i => allN (nat_lit 133) (fun j =>
    Nat.beq (fldW X (Nat.add (Nat.mul (nat_lit 1729) i) (Nat.mul (nat_lit 13) j)) (nat_lit 13))
      (nIf(Nat.beq i j, nat_lit 1, nat_lit 0))))

@[expose] noncomputable def validHN (X : Nat) : Bool :=
  CFSG.KC.Ord.validM (nat_lit 5) (nat_lit 229957) CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H X

end CFSG.KS.SporSch

end
