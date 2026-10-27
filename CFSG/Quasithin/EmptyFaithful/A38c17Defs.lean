module

public import CFSG.LieType.Universal.Unitary.Basic
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.Quasithin.A38c17

open Matrix CFSG.LieType.Universal.Unitary CFSG.Assembly.LowTwoRank

variable {F : Type*} [Field F]

@[expose] def GU (σ : F ≃+* F) (n : ℕ) : Subgroup (GL (Fin n) F) where
  carrier := {A | conjTr σ (A : Matrix (Fin n) (Fin n) F) * antidiag n *
    (A : Matrix (Fin n) (Fin n) F) = antidiag n}
  mul_mem' {A B} hA hB := by
    have e : conjTr σ ((A : Matrix (Fin n) (Fin n) F) * (B : Matrix (Fin n) (Fin n) F)) *
        antidiag n * ((A : Matrix (Fin n) (Fin n) F) * (B : Matrix (Fin n) (Fin n) F)) =
        conjTr σ (B : Matrix (Fin n) (Fin n) F) *
          (conjTr σ (A : Matrix (Fin n) (Fin n) F) * antidiag n * (A : Matrix (Fin n) (Fin n) F)) *
            (B : Matrix (Fin n) (Fin n) F) := by
      rw [conjTr_mul]
      simp only [Matrix.mul_assoc]
    show conjTr σ ((A * B : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * antidiag n *
      ((A * B : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = antidiag n
    rw [Units.val_mul, e, hA, hB]
  one_mem' := by
    show conjTr σ ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * antidiag n *
      ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = antidiag n
    simp [conjTr_one]
  inv_mem' {A} hA := by
    have hAB : (A : Matrix (Fin n) (Fin n) F) * ((A⁻¹ : GL (Fin n) F) : Matrix _ _ F) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have key : conjTr σ ((A⁻¹ : GL (Fin n) F) : Matrix _ _ F) *
        (conjTr σ (A : Matrix (Fin n) (Fin n) F) * antidiag n * (A : Matrix _ _ F)) *
          ((A⁻¹ : GL (Fin n) F) : Matrix _ _ F) =
        conjTr σ ((A : Matrix _ _ F) * ((A⁻¹ : GL (Fin n) F) : Matrix _ _ F)) * antidiag n *
          ((A : Matrix _ _ F) * ((A⁻¹ : GL (Fin n) F) : Matrix _ _ F)) := by
      rw [conjTr_mul]
      simp only [Matrix.mul_assoc]
    have hA' : conjTr σ (A : Matrix (Fin n) (Fin n) F) * antidiag n *
        (A : Matrix (Fin n) (Fin n) F) = antidiag n := hA
    show conjTr σ ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * antidiag n *
      ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = antidiag n
    rw [hA', hAB, conjTr_one, Matrix.one_mul, Matrix.mul_one] at key
    exact key

variable {σ : F ≃+* F}

theorem mem_GU {n : ℕ} {A : GL (Fin n) F} :
    A ∈ GU σ n ↔ conjTr σ (A : Matrix (Fin n) (Fin n) F) * antidiag n *
      (A : Matrix (Fin n) (Fin n) F) = antidiag n :=
  Iff.rfl

theorem mem_SU_iff_mem_GU_and_det {n : ℕ} {A : GL (Fin n) F} :
    A ∈ SU σ n ↔ A ∈ GU σ n ∧ (A : Matrix (Fin n) (Fin n) F).det = 1 :=
  ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

@[expose] def IsIrreducibleSU3 {K : Type} [Field K] {q : ℕ} (M : Subgroup ↥(StatedSU 3 q K)) :
    Prop :=
  ∀ W : Submodule K (Fin 3 → K),
    (∀ g ∈ M, ∀ w ∈ W, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w ∈ W) →
      W = ⊥ ∨ W = ⊤

end CFSG.Quasithin.A38c17
