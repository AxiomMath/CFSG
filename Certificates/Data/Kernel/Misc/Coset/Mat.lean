module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Basic

public section

namespace CFSG.KC.MiscCoset.Mat

@[expose] noncomputable def nthN (l : List Nat) (k : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun a _ ih k => Nat.rec (motive := fun _ => Nat) a (fun j _ => ih j) k) l k

@[expose] noncomputable def nthR (X : List (List Nat)) (i : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun r _ ih i => Nat.rec (motive := fun _ => List Nat) r (fun j _ => ih j) i) X i

@[expose] noncomputable def buildL {α : Type} (d : Nat) (f : Nat → α) (s : Nat) : List α :=
  Nat.rec (motive := fun _ => Nat → List α) (fun _ => [])
    (fun _ ih s => f s :: ih (Nat.succ s)) d s

@[expose] noncomputable def dotN (r : List Nat) (Y : List (List Nat)) (k : Nat) : Nat :=
  List.rec (motive := fun _ => List (List Nat) → Nat) (fun _ => 0)
    (fun a _ ih Y => List.rec (motive := fun _ => Nat) 0
      (fun row Y' _ => Nat.add (Nat.mul a (nthN row k)) (ih Y')) Y) r Y

@[expose] noncomputable def mulL (p d : Nat) (X Y : List (List Nat)) : List (List Nat) :=
  List.rec (motive := fun _ => List (List Nat)) []
    (fun r _ ih => buildL d (fun k => Nat.mod (dotN r Y k) p) 0 :: ih) X

@[expose] noncomputable def idL (d : Nat) : List (List Nat) :=
  buildL d (fun i => buildL d (fun j => Bool.rec (motive := fun _ => Nat) 0 1 (Nat.beq i j)) 0) 0

@[expose] noncomputable def wordL (p d : Nat) (L : Nat → List (List Nat)) (w : List Nat) :
    List (List Nat) :=
  List.rec (motive := fun _ => List (List Nat)) (idL d) (fun c _ ih => mulL p d (L c) ih) w

@[expose] noncomputable def eqN (l : List Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun l' => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) l')
    (fun a _ ih l' => List.rec (motive := fun _ => Bool) false
      (fun b t _ => Bool.rec (motive := fun _ => Bool) false (ih t) (Nat.beq a b)) l') l

@[expose] noncomputable def eqM (X : List (List Nat)) : List (List Nat) → Bool :=
  List.rec (motive := fun _ => List (List Nat) → Bool)
    (fun Y => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) Y)
    (fun r _ ih Y => List.rec (motive := fun _ => Bool) false
      (fun s t _ => Bool.rec (motive := fun _ => Bool) false (ih t) (eqN r s)) Y) X

@[expose] noncomputable def matL (p d : Nat) (X : List (List Nat)) : Matrix (Fin d) (Fin d) (ZMod p) :=
  Matrix.of fun i j => (nthN (nthR X i.val) j.val : ZMod p)

@[expose] noncomputable def rowsOf {p d : Nat} (M : Matrix (Fin d) (Fin d) (ZMod p)) :
    List (List Nat) :=
  (List.finRange d).map fun i => (List.finRange d).map fun j => ZMod.val (M i j)

end CFSG.KC.MiscCoset.Mat

end
