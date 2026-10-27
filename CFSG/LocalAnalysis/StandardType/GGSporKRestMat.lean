module

public import Mathlib.GroupTheory.Perm.Basic

public section

namespace CFSG.StandardType.SporadicShape.PermCover

open Equiv

@[expose] def mat {n : ℕ} (σ : Perm (Fin n)) : Perm (Fin n) :=
  let f : Array (Fin n) := Array.ofFn fun i => σ i
  let g : Array (Fin n) := Array.ofFn fun i => σ⁻¹ i
  ⟨fun i => f.getD i.1 i, fun i => g.getD i.1 i, fun i => by
      simp [f, g], fun i => by simp [f, g]⟩

theorem mat_eq {n : ℕ} (σ : Perm (Fin n)) : mat σ = σ := by
  ext i
  simp [mat]

@[expose] def permEq {n : ℕ} (x y : Perm (Fin n)) : Bool :=
  Nat.all n fun i hi => decide (x ⟨i, hi⟩ = y ⟨i, hi⟩)

theorem permEq_iff {n : ℕ} (x y : Perm (Fin n)) : permEq x y = true ↔ x = y := by
  rw [permEq, Nat.all_eq_finRange_all, List.all_eq_true]
  constructor
  · intro h
    ext i
    exact of_decide_eq_true (h i (List.mem_finRange i))
  · intro h a _
    show decide (x a = y a) = true
    rw [h]
    simp

@[expose] def permMem {n : ℕ} (x : Perm (Fin n)) (l : List (Perm (Fin n))) : Bool :=
  l.any (permEq x)

theorem permMem_iff {n : ℕ} (x : Perm (Fin n)) (l : List (Perm (Fin n))) :
    permMem x l = true ↔ x ∈ l := by
  rw [permMem, List.any_eq_true]
  constructor
  · rintro ⟨y, hy, hxy⟩
    have heq : x = y := (permEq_iff x y).mp hxy
    rw [heq]
    exact hy
  · rintro hx
    exact ⟨x, hx, (permEq_iff x x).mpr rfl⟩

@[expose] def permNodup {n : ℕ} : List (Perm (Fin n)) → Bool
  | [] => true
  | x :: l => !permMem x l && permNodup l

theorem permNodup_iff {n : ℕ} (l : List (Perm (Fin n))) : permNodup l = true ↔ l.Nodup := by
  induction l with
  | nil => simp [permNodup]
  | cons x l ih =>
    rw [permNodup, Bool.and_eq_true, List.nodup_cons, ih]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      intro hx
      have hx' : permMem x l = true := (permMem_iff x l).mpr hx
      rw [hx'] at h1
      simpa using h1
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      rw [Bool.not_eq_true_eq_eq_false]
      exact Bool.eq_false_iff.mpr fun h => h1 ((permMem_iff x l).mp h)

end CFSG.StandardType.SporadicShape.PermCover
