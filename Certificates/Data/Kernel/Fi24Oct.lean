module

public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.Fi24Oct

open CFSG.KC.Loop

@[expose] noncomputable def forceB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def nget (L : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun x _ ih i => Nat.rec (motive := fun _ => Nat) x (fun j _ => ih j) i) L

@[expose] noncomputable def allN (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => bAnd(f i, ih)) n

@[expose] noncomputable def bitN (m i : Nat) : Nat := Nat.land (Nat.shiftRight m i) 1

@[expose] noncomputable def bitB (m i : Nat) : Bool := Nat.beq (bitN m i) 1

@[expose] noncomputable def packK (w : Nat) (f : Nat → Nat) (L : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun x _ ih j => Nat.lor (Nat.shiftLeft (f x) (Nat.mul w j)) (ih (Nat.succ j))) L

@[expose] noncomputable def laneK (w Q i : Nat) : Nat :=
  Nat.land (Nat.shiftRight Q (Nat.mul w i)) (Nat.sub (Nat.shiftLeft 1 w) 1)

@[expose] noncomputable def low24 (x : Nat) : Nat :=
  Nat.land x (Nat.sub (Nat.shiftLeft 1 24) 1)

@[expose] noncomputable def pcK (m n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun i acc => Nat.add (bitN m i) acc) n

@[expose] noncomputable def cardOne (m : Nat) : Bool := Nat.beq (pcK m 24) 8

@[expose] noncomputable def cardStep (m : Nat) (b : Bool) : Bool := bAnd(cardOne m, b)

@[expose] noncomputable def cardK (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun m _ ih => cardStep m ih) L

@[expose] noncomputable def planesK (L : List Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => Nat.lor (Nat.shiftLeft (packK 1 (fun x => bitN x i) L 0)
      (Nat.mul 1024 i)) acc) 24

@[expose] noncomputable def thrK (Q m : Nat) (k : Nat → Nat → Nat → Nat → Nat → Bool) (n : Nat) :
    Nat → Nat → Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → Bool) k
    (fun i ih a b c d e => Bool.rec (motive := fun _ => Bool) (ih a b c d e)
      (forceB (laneK 1024 Q i) fun x =>
        forceB (Nat.lor a x) fun a' => forceB (Nat.lor b (Nat.land a x)) fun b' =>
        forceB (Nat.lor c (Nat.land b x)) fun c' => forceB (Nat.lor d (Nat.land c x)) fun d' =>
        forceB (Nat.lor e (Nat.land d x)) fun e' => ih a' b' c' d' e')
      (bitB m i)) n

@[expose] noncomputable def onlyK (k : Nat) : Nat → Nat → Nat → Nat → Nat → Bool :=
  fun _ _ _ _ e => Nat.beq (Nat.lor e (Nat.shiftLeft 1 k)) (Nat.shiftLeft 1 k)

@[expose] noncomputable def pairOneK (Q k m : Nat) : Bool :=
  thrK Q m (onlyK k) 24 0 0 0 0 0

@[expose] noncomputable def pairK (L : List Nat) : Bool :=
  forceB (planesK L) fun Q => forceB (packK 24 low24 L 0) fun W =>
    allN 759 fun k => pairOneK Q k (laneK 24 W k)

@[expose] noncomputable def imgK (P0 P1 : List Nat) (l m n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => Nat.lor (nIf(bitB m i, Nat.shiftLeft 1
      (Nat.mod (nIf(Nat.beq l 0, nget P0 i, nget P1 i)) 24), 0)) acc) n

@[expose] noncomputable def treeK (L P B P0 P1 : List Nat) : Bool :=
  forceB (packK 24 low24 L 0) fun W =>
  forceB (packK 16 (fun x => Nat.mod x 759) P 0) fun WP =>
  forceB (packK 1 (fun x => Nat.mod x 2) B 0) fun WB =>
  allN 759 fun k => bIf(Nat.beq k 0, true,
    bAnd(Nat.blt (laneK 16 WP k) k,
      Nat.beq (laneK 24 W k) (imgK P0 P1 (laneK 1 WB k)
        (laneK 24 W (laneK 16 WP k)) 24)))

end CFSG.KC.Fi24Oct

end
