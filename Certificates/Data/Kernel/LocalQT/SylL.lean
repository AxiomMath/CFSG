module

public import Certificates.Data.Kernel.LocalQT.SylE

public section

namespace CFSG.KC.LQT.Syl

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.S CFSG.KC.LQT.W CFSG.KC.LQT.T2

@[expose] noncomputable def eltK (n k : Nat) (B : List Nat) (m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun acc _ _ => acc)
    (fun _ ih acc d j => letN (Bool.rec (motive := fun _ => Nat) acc
      (mul n acc (getK B j (one n))) (Nat.beq (Nat.mod d 2) 1)) fun acc' =>
        ih acc' (Nat.div d 2) (Nat.succ j)) k (one n) m 0

@[expose] noncomputable def lstK (n k : Nat) (B : List Nat) : List Nat :=
  List.map (eltK n k B) (List.range (Nat.pow 2 k))

@[expose] noncomputable def eabK (n k : Nat) (B : List Nat) : Bool :=
  andB (subOK n k (lstK n k B) (lstK n k B))
    (allBs [allL (lstK n k B) (fun x => Nat.beq (mul n x x) (one n)),
      allL (lstK n k B) (fun x => allL (lstK n k B) fun y => comm n x y),
      allL B fun b => memL b (lstK n k B)])

@[expose] noncomputable def fgK (n cA cB : Nat) (RL : List Nat)
    (FG : List (Nat × Nat × List Int × List Int × List Int)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun f _ ih => andB
    (letB (evalZK n [cA, cB] f.2.2.1) fun c =>
      andB (Nat.beq (evalZK n [getK RL f.1 (one n), getK RL f.2.1 (one n),
          conj n c (getK RL f.1 (one n)), conj n c (getK RL f.2.1 (one n))] f.2.2.2.1) cA)
        (Nat.beq (evalZK n [getK RL f.1 (one n), getK RL f.2.1 (one n),
          conj n c (getK RL f.1 (one n)), conj n c (getK RL f.2.1 (one n))] f.2.2.2.2) cB)) ih) FG

end CFSG.KC.LQT.Syl

end
