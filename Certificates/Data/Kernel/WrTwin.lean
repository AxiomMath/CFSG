module

public import CFSG.ClassicalInvolution.Q3.AE.Wreath
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Tactic.Ring

public section

namespace CFSG.KC.WrTwin

open CFSG.ClassicalInvolution.Q3.AE

@[expose] def nib (x p : Nat) : Nat := x / 16 ^ p % 16

@[expose] def packL : List Nat → Nat
  | [] => 0
  | x :: l => x + 16 * packL l

@[expose] def pmul : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | m + 1, x, y => (x >>> (4 * (y % 16))) % 16 + 16 * pmul m x (y / 16)

@[expose] def img {n : Nat} (a : Wr n) (p : Nat) : Nat :=
  if h : p / 2 < n then
    2 * (a.perm ⟨p / 2, h⟩).val + (((p % 2 : Nat) : ZMod 2) + a.vec (a.perm ⟨p / 2, h⟩)).val
  else 0

@[expose] def enc {n : Nat} (a : Wr n) : Nat := packL ((List.range (2 * n)).map (img a))

@[expose] def pword (m e : Nat) (T : List Nat) (k : Nat) (W : List Nat) : Nat :=
  W.foldr (fun l acc => pmul m (T.getD (2 * k + l) 0) acc) e

@[expose] def rowL (m : Nat) (T Ti : List Nat) (d : Nat × Nat × Nat × Nat × List Nat) : Nat :=
  pmul m (pmul m (T.getD d.1 0) (T.getD (2 * d.2.1 + d.2.2.1) 0)) (Ti.getD d.1 0)

@[expose] def rowIdx (N : Nat) (d : Nat × Nat × Nat × Nat × List Nat) : Bool :=
  decide (d.1 < N) && decide (2 * d.2.1 + d.2.2.1 < N) &&
    d.2.2.2.2.all fun l => decide (2 * d.2.2.2.1 + l < N)

@[expose] def rowOK (m e N : Nat) (T Ti : List Nat) (d : Nat × Nat × Nat × Nat × List Nat) : Bool :=
  rowIdx N d && Nat.beq (rowL m T Ti d) (pword m e T d.2.2.2.1 d.2.2.2.2)

@[expose] def rowPiOK (m e pe N : Nat) (T Ti : List Nat) (d : Nat × Nat × Nat × Nat × List Nat) :
    Bool :=
  rowIdx N d && (Nat.beq (rowL m T Ti d) (pword m e T d.2.2.2.1 d.2.2.2.2) ||
    Nat.beq (rowL m T Ti d) (pmul m (pword m e T d.2.2.2.1 d.2.2.2.2) pe))

@[expose] def tabOK {n : Nat} (N : Nat) (T Ti : List Nat) (g : Nat → Wr n) : Bool :=
  (List.range N).all fun i => Nat.beq (T.getD i 0) (enc (g i)) && Nat.beq (Ti.getD i 0) (enc (g i)⁻¹)

@[expose] def chainProds {α : Type*} : List (List (Equiv.Perm α)) → List (Equiv.Perm α)
  | [] => [1]
  | E :: L => E.flatMap fun e => (chainProds L).map (e * ·)

@[expose] def chainOK {α : Type*} [DecidableEq α] (mem : Equiv.Perm α → Bool) :
    List α → List (List (Equiv.Perm α)) → Bool
  | _, [] => true
  | [], _ :: _ => false
  | b :: bs, E :: L =>
    E.all mem && decide (E.map (· b)).Nodup && L.all (·.all fun e => decide (e b = b)) &&
      chainOK mem bs L

end CFSG.KC.WrTwin

end
