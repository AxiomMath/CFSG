module

public import Certificates.Data.Kernel.SporSch.HNXPt

public section

namespace CFSG.KC.LL.HNX

open CFSG.KC.Loop CFSG.KC.LL

@[expose] noncomputable def packF (f : Nat → Nat) (lo c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Nat.lor acc (Nat.shiftLeft (f (Nat.add lo k)) (Nat.mul (nat_lit 21) k))) c

@[expose] noncomputable def bCnt (n b : Nat) : Nat :=
  nIf(Nat.ble (Nat.mul (nat_lit 64) (Nat.succ b)) n, nat_lit 64, Nat.sub n (Nat.mul (nat_lit 64) b))

@[expose] noncomputable def ptsFn (T : Nat → Nat) (MS CM3 M G : Nat) (f g : Nat → Nat) (n : Nat) :
    Bool :=
  CFSG.KC.Enum.allN (Nat.div (Nat.add n (nat_lit 63)) (nat_lit 64)) (fun b =>
    ptsImg T MS CM3 M G (packF f (Nat.mul (nat_lit 64) b) (bCnt n b))
      (packF g (Nat.mul (nat_lit 64) b) (bCnt n b)) (bCnt n b))

@[expose] def lget (P : List Nat) (k : Nat) : Nat := P.getD k 0

end CFSG.KC.LL.HNX

end
