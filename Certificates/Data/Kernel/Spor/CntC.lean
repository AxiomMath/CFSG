module

public import Certificates.Data.Kernel.SporSch.PairCl

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def commK (n w : Nat) (DP Ws : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun g _ ih => bAnd(allN n (fun i => Nat.beq (evRK w Ws (pg w (mask w) g i))
      (pg w (mask w) g (evRK w Ws i))), ih)) DP

@[expose] noncomputable def cntC3 (n w : Nat) (LR TR : Nat → Nat) (DP : List Nat) (k0 : Nat) : Nat :=
  strictN (Nat.mul n w) (fun nw => strictN (trK n nw LR TR 0 k0) (fun t0 =>
  foldUp (rcnt (LR 1)) (fun k1 s => strictN (trK n nw LR TR 1 k1) (fun t1 =>
    foldUp (rcnt (LR 2)) (fun k2 s => strictN (trK n nw LR TR 2 k2) (fun t2 =>
      nIf(commK n w DP [t2, t1, t0], Nat.succ s, s))) s)) (nat_lit 0)))

end CFSG.KS.SporSch

end
