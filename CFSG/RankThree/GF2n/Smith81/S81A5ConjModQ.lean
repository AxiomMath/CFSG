module

public import CFSG.RankThree.GF2n.Smith81.S81A5Basic

public section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

open Matrix exteriorPower

variable {K : Type*} [Field K]

@[expose] def NormalizesSL (T : Cube K ≃ₗ[K] Cube K) : Prop :=
  ∀ g : GL (Fin 6) K, (g : Matrix (Fin 6) (Fin 6) K).det = 1 →
    ∃ g' : GL (Fin 6) K, (g' : Matrix (Fin 6) (Fin 6) K).det = 1 ∧ ∀ ξ, T (rho K g ξ) = rho K g' (T ξ)

@[expose] def invTransp (g : GL (Fin 6) K) : GL (Fin 6) K where
  val := ((g⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)ᵀ
  inv := (g : Matrix (Fin 6) (Fin 6) K)ᵀ
  val_inv := by
    rw [← Matrix.transpose_mul]
    simp
  inv_val := by
    rw [← Matrix.transpose_mul]
    simp

@[expose] def A5NormalizerModelStatement : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (T : Cube K ≃ₗ[K] Cube K), NormalizesSL T →
    ∃ P : GL (Fin 6) K,
      (∀ g : GL (Fin 6) K, (g : Matrix (Fin 6) (Fin 6) K).det = 1 →
        ∀ ξ, T (rho K g ξ) = rho K (P * g * P⁻¹) (T ξ)) ∨
      (∀ g : GL (Fin 6) K, (g : Matrix (Fin 6) (Fin 6) K).det = 1 →
        ∀ ξ, T (rho K g ξ) = rho K (P * invTransp g * P⁻¹) (T ξ))

theorem rho_eq_of_twist {T : Cube K ≃ₗ[K] Cube K} {x y g' : GL (Fin 6) K}
    (hy : ∀ ξ, T (rho K x ξ) = rho K y (T ξ)) (hg' : ∀ ξ, T (rho K x ξ) = rho K g' (T ξ)) :
    rho K g' = rho K y := by
  refine LinearMap.ext fun η => ?_
  obtain ⟨ξ, rfl⟩ := T.surjective η
  exact (hg' ξ).symm.trans (hy ξ)

end CFSG.RankThree.GF2n.Smith81.A5Cube
