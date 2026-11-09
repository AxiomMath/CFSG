module

public import Certificates.Data.Kernel.OpsMcertN
public import Certificates.Data.Kernel.OpsLayMcert

public section

namespace CFSG.KC.OpsLayTab

open CFSG.SectionRank.Native CFSG.KC.OpsK CFSG.KC.OpsMN

inductive BTr (α : Type) where
  | nil : BTr α
  | leaf (a : α) : BTr α
  | node (l r : BTr α) : BTr α

@[expose] noncomputable def bget {α : Type} (z : α) (T : BTr α) (v : Nat) : α :=
  BTr.rec (motive := fun _ => Nat → α) (fun _ => z) (fun a _ => a)
    (fun _ _ il ir v => Bool.rec (motive := fun _ => α) (ir (Nat.div v 2)) (il (Nat.div v 2))
      (Nat.beq (Nat.mod v 2) 0)) T v

@[expose] noncomputable def tget {α : Type} (z : α) (T : BTr (BTr α)) (v : Nat) : α :=
  bget z (bget BTr.nil T (Nat.div v 64)) (Nat.mod v 64)

@[expose] noncomputable def entT {V : Type} (O : Ops Nat V) (T : BTr (BTr Nat))
    (k : Nat × Nat × Nat) (v : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool)
    (Nat.beq (tget 0 T v) (O.mul (tget 0 T k.2.1) (tget 0 T k.2.2)))
    (fun e _ => Nat.beq (tget 0 T v) (powN O (Nat.succ e) (tget 0 T k.2.1) e)) k.1

@[expose] noncomputable def entF (mu pw : Nat → Nat → Nat) (T : BTr (BTr Nat))
    (k : Nat × Nat × Nat) (v : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool)
    (Nat.beq (tget 0 T v) (mu (tget 0 T k.2.1) (tget 0 T k.2.2)))
    (fun e _ => Nat.beq (tget 0 T v) (pw (tget 0 T k.2.1) e)) k.1

@[expose] def keyAt (K v : Nat) : Nat × Nat × Nat :=
  (Nat.div (Nat.mod (Nat.shiftRight K (Nat.mul 48 v)) 281474976710656) 4294967296,
    Nat.mod (Nat.div (Nat.shiftRight K (Nat.mul 48 v)) 65536) 65536,
    Nat.mod (Nat.shiftRight K (Nat.mul 48 v)) 65536)

@[expose] noncomputable def tabT {V : Type} (O : Ops Nat V) (T : BTr (BTr Nat))
    (K N lo k : Nat) : Bool :=
  (List.range' lo k).all fun v => !Nat.blt v N || entT O T (keyAt K v) v

@[expose] noncomputable def tabF (mu pw : Nat → Nat → Nat) (T : BTr (BTr Nat))
    (K N lo k : Nat) : Bool :=
  (List.range' lo k).all fun v => !Nat.blt v N || entF mu pw T (keyAt K v) v

@[expose] def keyEq(k : Nat × Nat × Nat) (c a b : Nat) : Bool :=
  Nat.beq k.1 c && Nat.beq k.2.1 a && Nat.beq k.2.2 b

@[expose] def pget (P r : Nat) : Nat := Nat.mod (Nat.shiftRight P (Nat.mul 16 r)) 65536

@[expose] def pset (P t v : Nat) : Nat :=
  Nat.lor (Nat.lor (Nat.shiftLeft (Nat.shiftRight P (Nat.mul 16 (Nat.succ t)))
    (Nat.mul 16 (Nat.succ t))) (Nat.shiftLeft v (Nat.mul 16 t)))
    (Nat.mod P (Nat.shiftLeft 1 (Nat.mul 16 t)))

@[expose] noncomputable def regsT (T : BTr (BTr Nat)) (n P : Nat) : List Nat :=
  (List.range n).map fun r => tget 0 T (pget P r)

@[expose] noncomputable def opT (K N n P v : Nat) (op : Op) : Bool :=
  Nat.blt 2 v && Nat.blt v N && Nat.blt v 65536 &&
    Op.rec (motive := fun _ => Bool)
      (fun i j t => Nat.blt i n && Nat.blt j n && Nat.blt t n &&
        keyEq (keyAt K v) 0 (pget P i) (pget P j))
      (fun e i t => Nat.blt i n && Nat.blt t n &&
        keyEq (keyAt K v) (e + 1) (pget P i) 0) op

@[expose] noncomputable def tgtOf (op : Op) : Nat :=
  Op.rec (motive := fun _ => Nat) (fun _ _ t => t) (fun _ _ t => t) op

@[expose] noncomputable def symT (K N n : Nat) : List Op → List Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Nat → Nat → Bool)
    (fun vs P P' => List.rec (motive := fun _ => Bool) (Nat.beq P P') (fun _ _ _ => false) vs)
    (fun op _ ih vs P P' => List.rec (motive := fun _ => Bool) false
      (fun v vs' _ => opT K N n P v op && forceB (pset P (tgtOf op) v) fun Q => ih vs' Q P')
      vs)

end CFSG.KC.OpsLayTab

end
