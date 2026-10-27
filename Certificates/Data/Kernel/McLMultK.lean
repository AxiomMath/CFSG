module

public import Certificates.Data.Kernel.Spor.F3Lane

public section

namespace CFSG.KC.McLMult

open CFSG.F3.Native CFSG.KS.F3L CFSG.KC.Enum

@[expose] noncomputable def strictV {α : Type} (X : V) (k : V → α) : α :=
  strictT X.p fun p => strictT X.m fun m => k ⟨p, m⟩

@[expose] noncomputable def strictLs {α : Type} (L : List V) : (List V → α) → α :=
  List.rec (motive := fun _ => (List V → α) → α) (fun k => k [])
    (fun x _ ih k => strictV x fun x' => ih fun xs => k (x' :: xs)) L

@[expose] noncomputable def eqL (X Y : V) : Bool := bAnd(Nat.beq X.p Y.p, Nat.beq X.m Y.m)

@[expose] noncomputable def canonL (d : Nat) (X : V) : Bool :=
  bAnd(Nat.beq (Nat.land X.p X.m) (nat_lit 0),
    bAnd(Nat.blt X.p (Nat.shiftLeft (nat_lit 1) (Nat.mul d d)),
      Nat.blt X.m (Nat.shiftLeft (nat_lit 1) (Nat.mul d d))))

@[expose] noncomputable def idLane (d : Nat) : V :=
  ⟨Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.mul d i) i))) d, nat_lit 0⟩

@[expose] noncomputable def laneBody (cs : List Char) : Nat → Nat → Nat → V :=
  List.rec (motive := fun _ => Nat → Nat → Nat → V) (fun _ p m => ⟨p, m⟩)
    (fun ch _ ih k p m => strictT (Char.toNat ch) fun c =>
      Bool.rec (motive := fun _ => V)
        (strictT (Nat.mod (entK c) (nat_lit 3)) fun t =>
          strictT (nIf(Nat.beq t (nat_lit 1), Nat.lor p (Nat.shiftLeft (nat_lit 1) k), p)) fun p' =>
          strictT (nIf(Nat.beq t (nat_lit 2), Nat.lor m (Nat.shiftLeft (nat_lit 1) k), m)) fun m' =>
            ih (Nat.succ k) p' m')
        (ih k p m) (wsK c))
    cs

@[expose] noncomputable def laneOf (cs : List Char) : V :=
  List.rec (motive := fun _ => V) V.zero
    (fun ch rest ih => Bool.rec (motive := fun _ => V) ih
      (laneBody rest (nat_lit 0) (nat_lit 0) (nat_lit 0)) (Nat.beq (Char.toNat ch) (nat_lit 10))) cs

@[expose] noncomputable def mulL (d E : Nat) (X Y : V) : V := strictV (mulLane d E X Y) id

@[expose] noncomputable def abL (A B B4 : V) (z : Int) : V :=
  Int.rec (motive := fun _ => V)
    (fun k => Bool.rec (motive := fun _ => V) (Bool.rec (motive := fun _ => V) B4 B
      (Nat.beq k (nat_lit 2))) A (Nat.beq k (nat_lit 1)))
    (fun k => Bool.rec (motive := fun _ => V) B4 A (Nat.beq k (nat_lit 0))) z

@[expose] noncomputable def abK (d E : Nat) (I A B B4 : V) (w : List Int) : V :=
  List.rec (motive := fun _ => V) I (fun l _ ih => mulL d E (abL A B B4 l) ih) w

@[expose] noncomputable def evalK (d E : Nat) (I : V) (X Xi : Nat → V)
    (w : List (Fin 6 × Bool)) : V :=
  List.rec (motive := fun _ => V) I
    (fun l _ ih => mulL d E (Bool.rec (motive := fun _ => V) (Xi l.1.val) (X l.1.val) l.2) ih) w

@[expose] noncomputable def at6 (L : List V) (k : Nat) : V := L.getD k V.zero

@[expose] noncomputable def genCheck (d E : Nat) (I A B : V) (Y : List V)
    (rels : List (List (Fin 6 × Bool))) (comm : Fin 6 → List (Fin 6 × Bool))
    (sa sb : List (Fin 6 × Bool)) : Bool :=
  bAnd(rels.all (fun r => eqL (evalK d E I (at6 Y) (at6 Y) r) I),
    bAnd((List.finRange 6).all (fun i => eqL (evalK d E I (at6 Y) (at6 Y) (comm i)) (at6 Y i.val)),
      bAnd(eqL (evalK d E I (at6 Y) (at6 Y) sa) A, eqL (evalK d E I (at6 Y) (at6 Y) sb) B)))

@[expose] noncomputable def centralK (d E : Nat) (X : Nat → V) (R : V) : Bool :=
  (List.range 6).all fun j => eqL (mulL d E (X j) R) (mulL d E R (X j))

@[expose] noncomputable def orderThreeK (d E : Nat) (I Z : V) : Bool :=
  bAnd(canonL d Z, bAnd(Bool.not (eqL Z I), eqL (mulL d E Z (mulL d E Z Z)) I))

@[expose] noncomputable def coverCheck (d E : Nat) (I : V) (X Xi : List V)
    (rels : List (List (Fin 6 × Bool))) (comm : Fin 6 → List (Fin 6 × Bool))
    (z : List (Fin 6 × Bool)) : Bool :=
  bAnd((List.range 6).all (fun i => bAnd(canonL d (at6 X i), bAnd(canonL d (at6 Xi i),
      bAnd(eqL (mulL d E (at6 X i) (at6 Xi i)) I, eqL (mulL d E (at6 Xi i) (at6 X i)) I)))),
    bAnd(rels.all (fun r => centralK d E (at6 X) (evalK d E I (at6 X) (at6 Xi) r)),
      bAnd((List.finRange 6).all (fun i => eqL (evalK d E I (at6 X) (at6 Xi) (comm i)) (at6 X i.val)),
        orderThreeK d E I (evalK d E I (at6 X) (at6 Xi) z))))

end CFSG.KC.McLMult

end
