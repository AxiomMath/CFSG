module

public import Certificates.Data.Kernel.LocalQT.RankB

public section

namespace CFSG.KC.LQT.RB

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.S CFSG.KC.LQT.L CFSG.KC.LQT.PW CFSG.KC.LQT.BC
open CFSG.KC.LQT.PP CFSG.KC.LQT.BW CFSG.KC.LQT.BT CFSG.KC.LQT.RW CFSG.KC.LQT.RF

@[expose] noncomputable def letRQ (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k (nat_lit 0)) (fun m _ => k (Nat.succ m)) y

@[expose] noncomputable def mulRQ (W : Nat) (QT : Nat → Nat) (i k : Nat) : Nat := imgW W (QT i) k

@[expose] noncomputable def rowRQ (W g N : Nat) (PT CT QT : Nat → Nat) (i : Nat) : Bool :=
  letRQ (QT i) fun r => andB
    (allR 0 g fun j => letRQ (imgW W (QT (fieldT W CT j)) i) fun y =>
      andB (Nat.blt y N) (Nat.beq y (fieldT W CT (Nat.add (Nat.mul i (Nat.add g g)) j))))
    (Bool.rec (motive := fun _ => Bool)
      (andB (Nat.blt (fieldT W PT i) i) (letRQ (genIdxT W g (Nat.add g g) PT CT i) fun j =>
        andB (Nat.blt j g) (letRQ (QT (fieldT W CT j)) fun t => letRQ (QT (fieldT W PT i)) fun s =>
          Nat.beq r (mulW N W t s))))
      (allR 0 N fun k => Nat.beq (imgW W r k) k)
      (Nat.beq i 0))

@[expose] noncomputable def rankBQ (W N : Nat) (QT : Nat → Nat) (d zi lo len : Nat) : Bool :=
  (fun (invs : List Nat) => allL (sliceK invs lo len) (branchF (mulRQ W QT) invs zi d))
    (invsB N (mulRQ W QT))

end CFSG.KC.LQT.RB

end
