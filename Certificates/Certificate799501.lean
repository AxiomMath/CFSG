module

public import Certificates.Kernel.GL33T.Glue

public section

public section

namespace Certificates

theorem certificate799501 : ∀ (X : Subgroup (GL (Fin 3) (ZMod 3))) (v w₁ w₂ : Fin 3 → ZMod 3),
    LinearIndependent (ZMod 3) ![v, w₁, w₂] →
    (∃ τ ∈ X, Matrix.vecMul v (τ : Matrix (Fin 3) (Fin 3) (ZMod 3)) = v ∧
      Matrix.vecMul w₁ (τ : Matrix (Fin 3) (Fin 3) (ZMod 3)) = -w₁ ∧
      Matrix.vecMul w₂ (τ : Matrix (Fin 3) (Fin 3) (ZMod 3)) = -w₂) →
    Nat.card {g : GL (Fin 3) (ZMod 3) //
      g ∈ X ∧ Matrix.vecMul v (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) = v} = 8 →
    (∃ g ∈ X, ∃ h ∈ X, Matrix.vecMul v (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) = v ∧
      Matrix.vecMul v (h : Matrix (Fin 3) (Fin 3) (ZMod 3)) = v ∧ g * h ≠ h * g) →
    (∀ g ∈ X, (Matrix.vecMul v (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) = v ∨
        Matrix.vecMul v (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) = -v) →
      (∀ w ∈ Submodule.span (ZMod 3) {w₁, w₂},
        Matrix.vecMul w (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) ∈
          Submodule.span (ZMod 3) {w₁, w₂}) ∧
      ∃ d ∈ X, Matrix.vecMul v (d : Matrix (Fin 3) (Fin 3) (ZMod 3)) = v ∧
        ((∀ w ∈ Submodule.span (ZMod 3) {w₁, w₂},
            Matrix.vecMul w (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) =
              Matrix.vecMul w (d : Matrix (Fin 3) (Fin 3) (ZMod 3))) ∨
          ∀ w ∈ Submodule.span (ZMod 3) {w₁, w₂},
            Matrix.vecMul w (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) =
              -Matrix.vecMul w (d : Matrix (Fin 3) (Fin 3) (ZMod 3)))) →
    (∃ g ∈ X, Matrix.vecMul v (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) ≠ v ∧
      Matrix.vecMul v (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) ≠ -v) →
    ((∀ g ∈ X, ∀ w ∈ Submodule.span (ZMod 3) {w₁, w₂},
        Matrix.vecMul w (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) ∈
          Submodule.span (ZMod 3) {w₁, w₂}) ∧
      ∀ u : Fin 3 → ZMod 3, u ∉ Submodule.span (ZMod 3) {w₁, w₂} →
        ∃ g ∈ X, Matrix.vecMul v (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) = u ∨
          Matrix.vecMul v (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) = -u) ∨
    (∃ u₁ ∈ Submodule.span (ZMod 3) {w₁, w₂}, ∃ u₂ ∈ Submodule.span (ZMod 3) {w₁, w₂},
      LinearIndependent (ZMod 3) ![v, u₁, u₂] ∧
      (∀ g ∈ X, ∀ x ∈ ({v, -v, u₁, -u₁, u₂, -u₂} : Set (Fin 3 → ZMod 3)),
        Matrix.vecMul x (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) ∈
          ({v, -v, u₁, -u₁, u₂, -u₂} : Set (Fin 3 → ZMod 3))) ∧
      (∃ g ∈ X, Matrix.vecMul v (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) = -v ∧
        Matrix.vecMul u₁ (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) = u₁ ∧
        Matrix.vecMul u₂ (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) = u₂) ∧
      (∃ g ∈ X, Matrix.vecMul v (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) = u₁ ∧
        Matrix.vecMul u₁ (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) = v ∧
        Matrix.vecMul u₂ (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) = u₂) ∧
      (∃ g ∈ X, Matrix.vecMul v (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) = u₁ ∧
        Matrix.vecMul u₁ (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) = u₂ ∧
        Matrix.vecMul u₂ (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) = v)) :=
  CFSG.KD.GL33T.ff79

end Certificates

end
