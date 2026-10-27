module

public import Certificates.Data.Kernel.Spor.Fi24ThreeO

public section

namespace CFSG.KC.Fi24Oct

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.MonsterConv.Perm CFSG.KC.Fi24Net
  CFSG.KC.Fi24NetPt CFSG.KC.Fi24Kit CFSG.KC.Fi24ThreeO

@[expose] noncomputable def rootOK (NW : Nat → Nat → Nat) (NT : Nat → Nat)
    (we : List (List Nat × Nat)) : Bool :=
  allL (fun e => Nat.beq (ptC NW NT e.1 (nat_lit 0)) e.2) we

@[expose] noncomputable def commOK (NW : Nat → Nat → Nat) (NT : Nat → Nat)
    (we : List (List Nat × Nat)) : Bool :=
  allL (fun a => allL (fun b => Nat.beq (ptC NW NT (dW a.1) b.2) b.2) we) we

@[expose] noncomputable def pv (NW : Nat → Nat → Nat) (NT : Nat → Nat) (s : Nat) :
    List (List Nat × Nat) → List (Nat × Nat × Nat) :=
  List.rec (motive := fun _ => List (Nat × Nat × Nat)) List.nil
    (fun a t ih => List.rec (motive := fun _ => List (Nat × Nat × Nat)) ih
      (fun b _ jh => (a.2, b.2, ptC NW NT (dW a.1) (ptC NW NT (dW b.1) s)) :: jh) t)

@[expose] noncomputable def meetP (x y : Nat × Nat × Nat) : Bool :=
  orB (Nat.beq x.1 y.1) (orB (Nat.beq x.1 y.2.1) (orB (Nat.beq x.2.1 y.1) (Nat.beq x.2.1 y.2.1)))

@[expose] noncomputable def pairsOK (NW : Nat → Nat → Nat) (NT : Nat → Nat) (s : Nat)
    (we : List (List Nat × Nat)) : Bool :=
  allL (fun x => allL (fun y => orB (meetP x y) (notB (Nat.beq x.2.2 y.2.2))) (pv NW NT s we))
    (pv NW NT s we)

@[expose] noncomputable def normOK (NW : Nat → Nat → Nat) (NT : Nat → Nat) (N : List Nat)
    (pq : List (Nat × Nat)) : Bool :=
  allL (fun e => Nat.beq (ptC NW NT N e.1) e.2) pq

@[expose] noncomputable def prodC (ws : List (List Nat)) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil (fun w _ ih => dW w ++ ih) ws

@[expose] noncomputable def prodOK (NW : Nat → Nat → Nat) (NT : Nat → Nat) (ws : List (List Nat)) :
    Bool :=
  Nat.beq (fixC NW NT (prodC ws)) ptsM

end CFSG.KC.Fi24Oct

end
