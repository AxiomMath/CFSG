module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.RankThree.PartOne.N1322

open Matrix Equiv

variable {K : Type*} [Field K]

@[expose] def monoMat (σ : Perm (Fin 3)) (a : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.of fun i j => if i = σ j then a j else 0

theorem monoMat_apply (σ : Perm (Fin 3)) (a : Fin 3 → K) (i j : Fin 3) :
    monoMat σ a i j = if i = σ j then a j else 0 := rfl

theorem monoMat_mul (σ τ : Perm (Fin 3)) (a b : Fin 3 → K) :
    monoMat σ a * monoMat τ b = monoMat (σ * τ) (fun j => a (τ j) * b j) := by
  ext i j
  simp only [monoMat_apply, Matrix.mul_apply, Perm.mul_apply]
  rw [Finset.sum_eq_single (τ j)]
  · by_cases h : i = σ (τ j) <;> simp [h]
  · intro k _ hk
    simp [hk]
  · simp

theorem monoMat_one : monoMat (1 : Perm (Fin 3)) (fun _ => (1 : K)) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [monoMat_apply, Matrix.one_apply, h]

@[expose] def mono (σ : Perm (Fin 3)) (a : Fin 3 → Kˣ) : GL (Fin 3) K where
  val := monoMat σ (fun j => (a j : K))
  inv := monoMat σ⁻¹ (fun j => ((a (σ⁻¹ j))⁻¹ : Kˣ))
  val_inv := by
    rw [monoMat_mul, ← monoMat_one]
    congr 1
    · simp
    · funext j; simp
  inv_val := by
    rw [monoMat_mul, ← monoMat_one]
    congr 1
    · simp
    · funext j; simp

theorem mono_val (σ : Perm (Fin 3)) (a : Fin 3 → Kˣ) :
    ((mono σ a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = monoMat σ (fun j => (a j : K)) := rfl

theorem mono_mul (σ τ : Perm (Fin 3)) (a b : Fin 3 → Kˣ) :
    (mono σ a : GL (Fin 3) K) * mono τ b = mono (σ * τ) (fun j => a (τ j) * b j) := by
  ext1
  simp only [Units.val_mul, mono_val, monoMat_mul, Units.val_mul]

theorem mono_one : (mono (1 : Perm (Fin 3)) (fun _ => (1 : Kˣ)) : GL (Fin 3) K) = 1 := by
  ext1
  simp [mono_val, monoMat_one]

theorem mono_inv (σ : Perm (Fin 3)) (a : Fin 3 → Kˣ) :
    (mono σ a : GL (Fin 3) K)⁻¹ = mono σ⁻¹ (fun j => (a (σ⁻¹ j))⁻¹) := by
  rw [inv_eq_iff_mul_eq_one, mono_mul, ← mono_one]
  congr 1
  · simp
  · funext j; simp

theorem mono_injective {σ τ : Perm (Fin 3)} {a b : Fin 3 → Kˣ}
    (h : (mono σ a : GL (Fin 3) K) = mono τ b) : σ = τ ∧ a = b := by
  have hM : monoMat σ (fun j => (a j : K)) = monoMat τ (fun j => (b j : K)) := by
    have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) h
    simpa [mono_val] using this
  have hσ : σ = τ := by
    refine Equiv.ext fun j => ?_
    have hj := congrFun (congrFun hM (σ j)) j
    simp only [monoMat_apply, ite_true] at hj
    by_contra hne
    simp [hne] at hj
  subst hσ
  refine ⟨rfl, funext fun j => ?_⟩
  have hj := congrFun (congrFun hM (σ j)) j
  simp only [monoMat_apply, ite_true] at hj
  exact Units.ext hj

theorem mono_mulVec_single (σ : Perm (Fin 3)) (a : Fin 3 → Kˣ) (j : Fin 3) :
    ((mono σ a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single j (1 : K) =
      Pi.single (σ j) (a j : K) := by
  ext i
  simp [mono_val, monoMat_apply, Pi.single_apply]

end CFSG.RankThree.PartOne.N1322
