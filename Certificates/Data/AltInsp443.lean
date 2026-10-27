module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.GroupTheory.Perm.List
public import CFSG.Quasithin.Vol2.KGFactC31EBasis

public section

namespace CFSG.SectionRank.QTK.Insp443.Alt

open Equiv CFSG.Quasithin.KGC31

@[expose] def cyc5 (n : ℕ) [NeZero n] : Perm (Fin n) := List.formPerm [0, 1, 2, 3, 4]

@[expose] def cyc7 (n : ℕ) [NeZero n] : Perm (Fin n) := List.formPerm [0, 1, 2, 3, 4, 5, 6]

@[reducible, expose] def Bad (p : ℕ) {n : ℕ} (y s : Perm (Fin n)) : Prop :=
  y * s * y⁻¹ ≠ s ∧ ∀ j < p, s * (y ^ j * s * (y ^ j)⁻¹) = y ^ j * s * (y ^ j)⁻¹ * s

@[expose] def tri {n : ℕ} (y s : Perm (Fin n)) : Fin 3 → Perm (Fin n) :=
  ![s, y * s * y⁻¹, y ^ 2 * s * (y ^ 2)⁻¹]

@[reducible, expose] def Regular {n : ℕ} [NeZero n] (y s : Perm (Fin n)) : Prop :=
  (Finset.univ.image fun c : Fin 3 → ZMod 2 => eElt (tri y s) c 0).card = 8

@[reducible, expose] def SOK (n : ℕ) [NeZero n] (s : Perm (Fin n)) : Prop :=
  s * s = 1 → Perm.sign s = 1 →
    (∀ k < 5, ¬ Bad 5 (cyc5 n ^ k) s) ∧ ∀ k < 7, Bad 7 (cyc7 n ^ k) s → Regular (cyc7 n ^ k) s

instance (n : ℕ) [NeZero n] : DecidablePred (SOK n) := fun s => by
  unfold SOK
  infer_instance

@[reducible, expose] def AltProp (n : ℕ) [NeZero n] : Prop :=
  Perm.sign (cyc5 n) = 1 ∧ cyc5 n ^ 5 = 1 ∧ cyc5 n ≠ 1 ∧
    Perm.sign (cyc7 n) = 1 ∧ cyc7 n ^ 7 = 1 ∧ cyc7 n ≠ 1 ∧ ∀ s : Perm (Fin n), SOK n s

@[expose] def chk (n : ℕ) [NeZero n] (_ : Unit := ()) : Bool := decide (AltProp n)

theorem altProp_of_chk {n : ℕ} [NeZero n] (h : chk n () = true) : AltProp n :=
  of_decide_eq_true h

end CFSG.SectionRank.QTK.Insp443.Alt

end
