module

public import Certificates.Data.Kernel.LocalQT.Syl

public section

namespace CFSG.KC.LQT.Syl

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.S CFSG.KC.LQT.W CFSG.KC.LQT.T2

@[expose] noncomputable def letN (y : Nat) (k : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (k (nat_lit 0)) (fun m _ => k (Nat.succ m)) y

@[expose] noncomputable def sqK (n x a : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun y => y) (fun _ ih y => letN (mul n y y) ih) a x

@[expose] noncomputable def sylG2K (n a : Nat) (RL G : List Nat) : Bool :=
  allBs [Nat.ble n 32, Nat.beq (lenL RL) (Nat.pow 2 a), distinctS RL, memL (one n) RL,
    allL RL (fun x => Nat.beq (sqK n x a) (one n)),
    allL G fun g => eqL (sortK (List.map (fun x => mul n x g) RL)) (sortK RL)]

@[expose] noncomputable def toNatK (z : Int) : Nat := Int.rec (motive := fun _ => Nat) (fun m => m) (fun _ => 0) z

@[expose] noncomputable def conjP (n : Nat) (pool : List Nat) (ws : List (List Int)) : List Nat :=
  List.map (fun w => getK pool (toNatK (List.rec (motive := fun _ => Int) 0 (fun z _ _ => z) w))
    (one n)) ws

@[expose] noncomputable def g1okPK (n : Nat) (pool RL : List Nat)
    (G1 : List (Nat × List (List Int) × List Nat)) (p : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun e _ ih => andB (andB (Nat.beq (lenK e.2.1) 2)
    (witK n [getK RL e.1 (one n)] (conjP n pool e.2.1) e.2.2 p)) ih) G1

@[expose] noncomputable def g2okPK (n : Nat) (pool RL : List Nat)
    (G2 : List (Nat × Nat × List (List Int) × List Nat)) (p : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun e _ ih => andB (andB (Nat.beq (lenK e.2.2.1) 1)
    (witK n [getK RL e.1 (one n), getK RL e.2.1 (one n)] (conjP n pool e.2.2.1) e.2.2.2 p)) ih) G2

@[expose] noncomputable def badOne (n : Nat) (RL : List Nat) (RP : List (Nat × Nat)) (m : Nat)
    (x q : Nat × Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) 1
    (Bool.rec (motive := fun _ => Nat) 1099511627776 0
      (andB (Nat.blt q.2 (lenL RL))
        (letB (getK RL q.2 (one n)) fun r =>
          andB (Nat.beq (conj n r x.1) (getK RP q.1 (0, 0)).1)
            (Nat.beq (conj n r x.2) (getK RP q.1 (0, 0)).2))))
    (Nat.blt q.1 m)

@[expose] noncomputable def letQ (y : Nat) (k : Nat → List (Nat × Nat)) : List (Nat × Nat) :=
  Nat.rec (motive := fun _ => List (Nat × Nat)) (k (nat_lit 0)) (fun m _ => k (Nat.succ m)) y

@[expose] noncomputable def chunkK (c : Nat) : List (Nat × Nat) :=
  Nat.rec (motive := fun _ => Nat → List (Nat × Nat)) (fun _ => [])
    (fun _ ih d => List.cons (Nat.mod (Nat.div d 1024) 1024, Nat.mod d 1024)
      (letQ (Nat.div d 1048576) ih)) 4 c

@[expose] noncomputable def unpackK (L : Nat) (cs : List Nat) : List (Nat × Nat) :=
  List.take L (List.flatten (List.map chunkK cs))

@[expose] noncomputable def lenIs {α : Type} (l : List α) (c : Nat) : Bool := Nat.beq (lenK l) c

@[expose] noncomputable def atMost (x c : Nat) : Bool := Nat.ble x c

@[expose] noncomputable def badK (n : Nat) (RL : List Nat)
    (G2 : List (Nat × Nat × List (List Int) × List Nat)) (hs : List (Nat × Nat)) : Nat :=
  List.rec (motive := fun _ => List (Nat × Nat) → Nat → Nat)
    (fun h acc => List.rec (motive := fun _ => Nat) acc (fun _ _ _ => Nat.add acc 1099511627776) h)
    (fun x _ ih h acc => List.rec (motive := fun _ => Nat) (Nat.add acc 1099511627776)
      (fun q qs _ => letN (Nat.add acc (badOne n RL
        (List.map (fun e => (getK RL e.1 (one n), getK RL e.2.1 (one n))) G2) (lenK G2) x q))
        (ih qs)) h)
    (pairK n (invK n RL)) hs 0

end CFSG.KC.LQT.Syl

end
