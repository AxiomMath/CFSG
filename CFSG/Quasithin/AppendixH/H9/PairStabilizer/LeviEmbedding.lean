module

public import CFSG.Quasithin.AppendixH.H9.SylowModel
public import CFSG.Quasithin.AppendixH.H9.AutPair.LeviEmbedding

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH.PairStab

open CFSG.ASVolI.ChH.AutPair

variable {m : ℕ}

theorem leviMat_mulVec_zero (B : Matrix (Fin m) (Fin m) (ZMod 2)) (x : Fin (m + 1) → ZMod 2) :
    (leviMat B *ᵥ x) 0 = x 0 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem leviMat_mulVec_succ (B : Matrix (Fin m) (Fin m) (ZMod 2)) (x : Fin (m + 1) → ZMod 2)
    (i : Fin m) : (leviMat B *ᵥ x) i.succ = (B *ᵥ fun j => x j.succ) i := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem ez_zero : ez m 0 = 1 := by simp [ez]

theorem levi_mulVec_ez (B : GL (Fin m) (ZMod 2)) :
    ((levi m B : GL (Fin (m + 1)) (ZMod 2)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) *ᵥ
      ez m = ez m :=
  levi_mulVec_single B

theorem levi_mem_utriGL_iff {B : GL (Fin m) (ZMod 2)} :
    levi m B ∈ utriGL (m + 1) ↔ B ∈ utriGL m := by
  rw [mem_utriGL_iff, mem_utriGL_iff, levi_val]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j hji => ?_, fun i => ?_⟩
    · have := h1 i.succ j.succ (Fin.succ_lt_succ_iff.mpr hji)
      simpa using this
    · have := h2 i.succ
      simpa using this
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j hji => ?_, fun i => ?_⟩
    · induction i using Fin.cases with
      | zero => exact absurd hji (by simp)
      | succ i =>
        induction j using Fin.cases with
        | zero => simp
        | succ j =>
          have hj : j < i := Fin.succ_lt_succ_iff.mp hji
          simpa using h1 i j hj
    · induction i using Fin.cases with
      | zero => simp
      | succ i => simpa using h2 i

