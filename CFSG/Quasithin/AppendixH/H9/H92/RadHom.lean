module

public import CFSG.Quasithin.AppendixH.H9.H92.RadDefs
public import CFSG.Quasithin.AppendixH.H9.H92.RadCard.HomMatDim

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

@[expose] def homMat (n : ℕ) (D' E : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Submodule (ZMod 2) (Matrix (Fin n) (Fin n) (ZMod 2)) where
  carrier := {N | (∀ x : Fin n → ZMod 2, N *ᵥ x ∈ D') ∧ ∀ u ∈ E, N *ᵥ u = 0}
  add_mem' := by
    rintro N N' ⟨hN1, hN2⟩ ⟨hN1', hN2'⟩
    refine ⟨fun x => ?_, fun u hu => ?_⟩
    · rw [Matrix.add_mulVec]
      exact D'.add_mem (hN1 x) (hN1' x)
    · rw [Matrix.add_mulVec, hN2 u hu, hN2' u hu, add_zero]
  zero_mem' := by
    refine ⟨fun x => ?_, fun u _ => ?_⟩
    · rw [Matrix.zero_mulVec]
      exact D'.zero_mem
    · rw [Matrix.zero_mulVec]
  smul_mem' := by
    rintro c N ⟨hN1, hN2⟩
    refine ⟨fun x => ?_, fun u hu => ?_⟩
    · rw [Matrix.smul_mulVec]
      exact D'.smul_mem c (hN1 x)
    · rw [Matrix.smul_mulVec, hN2 u hu, smul_zero]

theorem mem_homMat {n : ℕ} {D' E : Submodule (ZMod 2) (Fin n → ZMod 2)}
    {N : Matrix (Fin n) (Fin n) (ZMod 2)} :
    N ∈ homMat n D' E ↔ (∀ x : Fin n → ZMod 2, N *ᵥ x ∈ D') ∧ ∀ u ∈ E, N *ᵥ u = 0 := Iff.rfl

theorem finrank_homMat (n : ℕ) (D' E : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Module.finrank (ZMod 2) (homMat n D' E) =
      (n - Module.finrank (ZMod 2) E) * Module.finrank (ZMod 2) D' :=
  finrank_matrix_of_mulVec_mem_and_kills D' E (homMat n D' E) fun _ => Iff.rfl

abbrev radNil (n : ℕ) (D : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Submodule (ZMod 2) (Matrix (Fin n) (Fin n) (ZMod 2)) := homMat n D D

theorem mem_radNil {n : ℕ} {D : Submodule (ZMod 2) (Fin n → ZMod 2)}
    {N : Matrix (Fin n) (Fin n) (ZMod 2)} :
    N ∈ radNil n D ↔ (∀ x : Fin n → ZMod 2, N *ᵥ x ∈ D) ∧ ∀ u ∈ D, N *ᵥ u = 0 := Iff.rfl

theorem finrank_radNil (n : ℕ) (D : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Module.finrank (ZMod 2) (radNil n D) =
      (n - Module.finrank (ZMod 2) D) * Module.finrank (ZMod 2) D :=
  finrank_homMat n D D

theorem radNil_mul_radNil {n : ℕ} {D : Submodule (ZMod 2) (Fin n → ZMod 2)}
    {N N' : Matrix (Fin n) (Fin n) (ZMod 2)} (hN : N ∈ radNil n D) (hN' : N' ∈ radNil n D) :
    N * N' = 0 := by
  refine Matrix.ext fun i j => ?_
  have h := congrFun (hN.2 _ (hN'.1 (Pi.single j 1))) i
  have h2 : (N * N') *ᵥ (Pi.single j 1 : Fin n → ZMod 2) = N *ᵥ (N' *ᵥ (Pi.single j 1)) := by
    rw [Matrix.mulVec_mulVec]
  rw [← h2, Matrix.mulVec_single_one] at h
  simpa using h

theorem mem_radMat_iff_sub_mem_radNil {n : ℕ} {D : Submodule (ZMod 2) (Fin n → ZMod 2)}
    (B : GL (Fin n) (ZMod 2)) :
    B ∈ RadMat n D ↔ (B : Matrix (Fin n) (Fin n) (ZMod 2)) - 1 ∈ radNil n D := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun u hu => ?_⟩
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, h2 u hu, sub_self]
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun u hu => ?_⟩
    have h := h2 u hu
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h
    exact h

theorem exists_radMat_of_mem_radNil {n : ℕ} {D : Submodule (ZMod 2) (Fin n → ZMod 2)}
    {N : Matrix (Fin n) (Fin n) (ZMod 2)} (hN : N ∈ radNil n D) :
    ∃ B ∈ RadMat n D, (B : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 + N := by
  have hNN : N * N = 0 := radNil_mul_radNil hN hN
  have h2 : ∀ M : Matrix (Fin n) (Fin n) (ZMod 2), M + M = 0 := by
    intro M
    ext i j
    simp only [Matrix.add_apply, Matrix.zero_apply]
    exact (by decide : ∀ c : ZMod 2, c + c = 0) _
  have hmul : (1 + N) * (1 + N) = 1 := by
    have e : (1 + N) * (1 + N) = 1 + (N + N) + N * N := by noncomm_ring
    rw [e, h2 N, hNN, add_zero, add_zero]
  refine ⟨⟨1 + N, 1 + N, hmul, hmul⟩, ?_, rfl⟩
  rw [mem_radMat_iff_sub_mem_radNil]
  have e : ((1 + N : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) = N := by abel
  show (1 + N : Matrix (Fin n) (Fin n) (ZMod 2)) - 1 ∈ radNil n D
  rw [e]
  exact hN

end CFSG.ASVolI.ChH
