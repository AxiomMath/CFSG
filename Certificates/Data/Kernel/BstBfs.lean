module

public import Certificates.Data.Kernel.S97RYK

public section

namespace CFSG.KC.BstBfs

open CFSG.KC.S97RYK

inductive BT where
  | lf : BT
  | nd : BT → Nat → BT → BT

@[expose] noncomputable def memB (t : BT) (y : Nat) : Bool :=
  BT.rec (motive := fun _ => Bool) false
    (fun _ v _ ihl ihr => bIfK (Nat.blt y v) ihl (bIfK (Nat.blt v y) ihr true)) t

@[expose] noncomputable def insC {α : Type} (t : BT) (y : Nat) (k : BT → α) : α :=
  BT.rec (motive := fun _ => (BT → α) → α) (fun k => k (BT.nd BT.lf y BT.lf))
    (fun l v r ihl ihr k => bIfK (Nat.blt y v) (ihl fun l' => k (BT.nd l' v r))
      (bIfK (Nat.blt v y) (ihr fun r' => k (BT.nd l v r')) (k (BT.nd l v r)))) t k

@[expose] noncomputable def inorder (t : BT) : List Nat → List Nat :=
  BT.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun _ v _ ihl ihr acc => ihl (v :: ihr acc)) t

@[expose] noncomputable def stepB (mul : Nat → Nat → Nat) (x : Nat) {α : Type} (gs : List Nat) :
    BT → List Nat → (BT → List Nat → α) → α :=
  List.rec (motive := fun _ => BT → List Nat → (BT → List Nat → α) → α) (fun t F k => k t F)
    (fun s _ ih t F k => strictK (mul x s) fun y =>
      bIfK (memB t y) (ih t F k) (insC t y fun t' => ih t' (y :: F) k)) gs

@[expose] noncomputable def roundB (mul : Nat → Nat → Nat) {α : Type} (gs fr : List Nat) :
    BT → List Nat → (BT → List Nat → α) → α :=
  List.rec (motive := fun _ => BT → List Nat → (BT → List Nat → α) → α) (fun t F k => k t F)
    (fun x _ ih t F k => stepB mul x gs t F fun t F => ih t F k) fr

@[expose] noncomputable def bfsB (mul : Nat → Nat → Nat) {α : Type} (gs : List Nat) (fuel : Nat) :
    BT → List Nat → (BT → α) → α :=
  Nat.rec (motive := fun _ => BT → List Nat → (BT → α) → α) (fun t _ k => k t)
    (fun _ ih t fr k => roundB mul gs fr t [] fun t F =>
      List.rec (motive := fun _ => α) (k t) (fun _ _ _ => ih t F k) F) fuel

@[expose] noncomputable def sincK (L : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih p => bIfK (Nat.blt p x) (ih x) false) L

@[expose] noncomputable def sincL (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x xs _ => sincK xs x) L

end CFSG.KC.BstBfs

end
