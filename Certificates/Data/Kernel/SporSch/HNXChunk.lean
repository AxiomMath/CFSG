module

public import CFSG.Certificates.Kernel.Local.LargeCore.Grp

public section

namespace CFSG.KC.LL.HNX

open CFSG.KC.LL

@[expose] noncomputable def sliceP (P m : Nat) : Nat :=
  fldW P (Nat.mul (nat_lit 1344) m) (nat_lit 1344)

@[expose] noncomputable def imgP (P S m c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft
      (fldW P (Nat.mul (nat_lit 21) (fldW S (Nat.mul (nat_lit 14)
        (Nat.add (Nat.mul (nat_lit 64) m) i)) (nat_lit 14))) (nat_lit 21))
      (Nat.mul (nat_lit 21) i))) c

@[expose] noncomputable def cntP (N m : Nat) : Nat :=
  Nat.min (nat_lit 64) (Nat.sub N (Nat.mul (nat_lit 64) m))

end CFSG.KC.LL.HNX

end
