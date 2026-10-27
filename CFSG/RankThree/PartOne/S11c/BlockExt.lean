module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.RankThree.PartOne.HNRed

open Matrix

section Incl

variable (K : Type*) [Field K] {ι κ : Type*} [DecidableEq ι]

@[expose] def incl (e : κ ↪ ι) : Matrix ι κ K := Matrix.of fun a s => if e s = a then 1 else 0

variable {K}

theorem incl_mulVec [Fintype κ] (e : κ ↪ ι) (u : κ → K) (a : ι) :
    (incl K e *ᵥ u) a = ∑ s, if e s = a then u s else 0 := by
  simp [incl, Matrix.mulVec, dotProduct, ite_mul]

theorem incl_mulVec_emb [Fintype κ] [DecidableEq κ] (e : κ ↪ ι) (u : κ → K) (s : κ) :
    (incl K e *ᵥ u) (e s) = u s := by
  rw [incl_mulVec, Finset.sum_eq_single s]
  · simp
  · intro t _ ht
    simp [e.injective.ne ht]
  · simp

theorem incl_mulVec_of_ne [Fintype κ] (e : κ ↪ ι) (u : κ → K) (a : ι) (ha : ∀ s, e s ≠ a) :
    (incl K e *ᵥ u) a = 0 := by
  rw [incl_mulVec]
  exact Finset.sum_eq_zero fun s _ => by simp [ha s]

theorem inclT_mulVec [Fintype ι] (e : κ ↪ ι) (v : ι → K) (s : κ) :
    ((incl K e)ᵀ *ᵥ v) s = v (e s) := by
  simp [incl, Matrix.mulVec, dotProduct, Matrix.transpose_apply]

theorem inclT_mul_incl [Fintype ι] [Fintype κ] [DecidableEq κ] (e : κ ↪ ι) :
    (incl K e)ᵀ * incl K e = 1 := by
  ext s t
  simp only [Matrix.mul_apply, Matrix.transpose_apply, incl, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (e s)]
  · by_cases h : s = t
    · simp [h]
    · simp [h, Ne.symm h]
  · intro a _ ha
    simp [Ne.symm ha]
  · simp

theorem inclT_mul_incl_of_disjoint [Fintype ι] [Fintype κ] {κ' : Type*} [Fintype κ']
    (e : κ ↪ ι) (e' : κ' ↪ ι) (h : ∀ s t, e s ≠ e' t) : (incl K e)ᵀ * incl K e' = 0 := by
  ext s t
  simp only [Matrix.mul_apply, Matrix.transpose_apply, incl, Matrix.of_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun a _ => ?_
  by_cases h1 : e s = a
  · have : e' t ≠ a := fun h2 => h s t (h1.trans h2.symm)
    simp [this]
  · simp [h1]

end Incl

section BlockExt

variable {K : Type*} [Field K] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ]

@[expose] def blockExt (e : κ ↪ ι) (M : Matrix κ κ K) : Matrix ι ι K :=
  1 + incl K e * (M - 1) * (incl K e)ᵀ

omit [Fintype ι] in
theorem blockExt_one (e : κ ↪ ι) : blockExt e (1 : Matrix κ κ K) = 1 := by
  simp [blockExt]

theorem blockExt_mul (e : κ ↪ ι) (M N : Matrix κ κ K) :
    blockExt e M * blockExt e N = blockExt e (M * N) := by
  have h := inclT_mul_incl (K := K) e
  have key : incl K e * (M - 1) * (incl K e)ᵀ * (incl K e * (N - 1) * (incl K e)ᵀ) =
      incl K e * ((M - 1) * (N - 1)) * (incl K e)ᵀ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (incl K e)ᵀ (incl K e), h, Matrix.one_mul]
  have hMN : M * N - 1 = (M - 1) + (N - 1) + (M - 1) * (N - 1) := by noncomm_ring
  unfold blockExt
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, key, hMN]
  abel

@[expose] def blockExtHom (e : κ ↪ ι) : Matrix κ κ K →* Matrix ι ι K where
  toFun := blockExt e
  map_one' := blockExt_one e
  map_mul' M N := (blockExt_mul e M N).symm

theorem blockExt_commute {κ' : Type*} [Fintype κ'] [DecidableEq κ'] (e : κ ↪ ι) (e' : κ' ↪ ι)
    (h : ∀ s t, e s ≠ e' t) (M : Matrix κ κ K) (N : Matrix κ' κ' K) :
    blockExt e M * blockExt e' N = blockExt e' N * blockExt e M := by
  have h1 : (incl K e)ᵀ * incl K e' = 0 := inclT_mul_incl_of_disjoint e e' h
  have h2 : (incl K e')ᵀ * incl K e = 0 := by
    have := congrArg Matrix.transpose h1
    simpa [Matrix.transpose_mul] using this
  have k1 : incl K e * (M - 1) * (incl K e)ᵀ * (incl K e' * (N - 1) * (incl K e')ᵀ) = 0 := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (incl K e)ᵀ (incl K e'), h1, Matrix.zero_mul]
    simp
  have k2 : incl K e' * (N - 1) * (incl K e')ᵀ * (incl K e * (M - 1) * (incl K e)ᵀ) = 0 := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (incl K e')ᵀ (incl K e), h2, Matrix.zero_mul]
    simp
  unfold blockExt
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, k1, k2]
  abel

theorem blockExt_mulVec (e : κ ↪ ι) (M : Matrix κ κ K) (v : ι → K) :
    blockExt e M *ᵥ v = v + incl K e *ᵥ ((M - 1) *ᵥ ((incl K e)ᵀ *ᵥ v)) := by
  unfold blockExt
  rw [Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

theorem inclT_mulVec_incl (e : κ ↪ ι) (u : κ → K) : (incl K e)ᵀ *ᵥ (incl K e *ᵥ u) = u := by
  rw [Matrix.mulVec_mulVec, inclT_mul_incl, Matrix.one_mulVec]

theorem blockExt_mulVec_incl (e : κ ↪ ι) (M : Matrix κ κ K) (u : κ → K) :
    blockExt e M *ᵥ (incl K e *ᵥ u) = incl K e *ᵥ (M *ᵥ u) := by
  rw [blockExt_mulVec, inclT_mulVec_incl, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub]
  abel

theorem blockExt_mulVec_incl_of_disjoint {κ' : Type*} [Fintype κ'] (e : κ ↪ ι) (e' : κ' ↪ ι)
    (h : ∀ s t, e s ≠ e' t) (M : Matrix κ κ K) (u : κ' → K) :
    blockExt e M *ᵥ (incl K e' *ᵥ u) = incl K e' *ᵥ u := by
  have h1 : (incl K e)ᵀ * incl K e' = 0 := inclT_mul_incl_of_disjoint e e' h
  rw [blockExt_mulVec]
  have : (incl K e)ᵀ *ᵥ (incl K e' *ᵥ u) = 0 := by
    rw [Matrix.mulVec_mulVec, h1, Matrix.zero_mulVec]
  rw [this, Matrix.mulVec_zero, Matrix.mulVec_zero, add_zero]

theorem inclT_blockExt_incl (e : κ ↪ ι) (M : Matrix κ κ K) :
    (incl K e)ᵀ * blockExt e M * incl K e = M := by
  have h := inclT_mul_incl (K := K) e
  have h2 : (incl K e)ᵀ * (incl K e * (M - 1) * (incl K e)ᵀ) * incl K e = M - 1 := by
    calc (incl K e)ᵀ * (incl K e * (M - 1) * (incl K e)ᵀ) * incl K e =
        ((incl K e)ᵀ * incl K e) * (M - 1) * ((incl K e)ᵀ * incl K e) := by
          simp only [Matrix.mul_assoc]
      _ = M - 1 := by rw [h]; simp
  unfold blockExt
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, h, h2]
  abel

@[expose] def blockGL (e : κ ↪ ι) :
    Matrix.GeneralLinearGroup κ K →* Matrix.GeneralLinearGroup ι K :=
  Units.map (blockExtHom e)

theorem blockGL_coe (e : κ ↪ ι) (g : Matrix.GeneralLinearGroup κ K) :
    ((blockGL e g : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) =
      blockExt e (g : Matrix κ κ K) := rfl

theorem blockGL_injective (e : κ ↪ ι) : Function.Injective (blockGL (K := K) e) := by
  intro g g' h
  apply Units.ext
  have h1 := congrArg (fun A : Matrix.GeneralLinearGroup ι K => (incl K e)ᵀ * (A : Matrix ι ι K) *
    incl K e) h
  simpa only [blockGL_coe, inclT_blockExt_incl] using h1

theorem blockGL_commute {κ' : Type*} [Fintype κ'] [DecidableEq κ'] (e : κ ↪ ι) (e' : κ' ↪ ι)
    (h : ∀ s t, e s ≠ e' t) (g : Matrix.GeneralLinearGroup κ K)
    (g' : Matrix.GeneralLinearGroup κ' K) : blockGL e g * blockGL e' g' = blockGL e' g' *
      blockGL e g := by
  apply Units.ext
  simp only [Units.val_mul, blockGL_coe]
  exact blockExt_commute e e' h _ _

end BlockExt

end CFSG.RankThree.PartOne.HNRed
