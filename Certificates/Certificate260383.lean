module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import CFSG.Certificates.Kernel.B45L33Sound
import Certificates.Kernel.B45L33.Checks

public section

namespace Certificates

open CFSG.KC.B45L33 CertificateChecks.KD.B45L33

open Matrix in
theorem certificate260383 :
    (∀ (K : Type) [Field K] [CharP K 3], (∀ k : K, ∃ n : ℕ, n < 3 ∧ (n : K) = k) →
      ∀ A : Matrix (Fin 3) (Fin 3) K, Aᵀ = A → A.det ≠ 0 →
        ∃ Y : Matrix (Fin 3) (Fin 3) K, Y.det = 1 ∧ Y * A = A * Yᵀ ∧ Y ^ 13 = 1 ∧ Y ≠ 1) ∧
    (∀ (K : Type) [Field K] [CharP K 3], (∀ k : K, ∃ n : ℕ, n < 3 ∧ (n : K) = k) →
      ∀ T U : Matrix (Fin 3) (Fin 3) K, T.det = 1 → U.det = 1 → T * T = 1 → T ≠ 1 →
        U * U = 1 → U ≠ 1 → T ≠ U → T * U = U * T →
        ∃ G Gi : Matrix (Fin 3) (Fin 3) K, G.det = 1 ∧ G * T = T * G ∧ G * Gi = 1 ∧
          (U * (G * U * Gi)) ^ 4 = 1 ∧ (U * (G * U * Gi)) ^ 2 ≠ 1) ∧
    (∀ (K : Type) [Field K] [CharP K 3], (∀ k : K, ∃ n : ℕ, n < 3 ∧ (n : K) = k) →
      ∀ A T U : Matrix (Fin 3) (Fin 3) K, Aᵀ = A → A.det ≠ 0 → T.det = 1 → U.det = 1 →
        T * T = 1 → T ≠ 1 → U * U = 1 → U ≠ 1 → T ≠ U → T * U = U * T → T * A * Tᵀ = A →
        U * A * Uᵀ = A →
        ∃ X₁ Y₁ X₂ Y₂ X₃ Y₃ : Matrix (Fin 3) (Fin 3) K, X₁.det = 1 ∧ X₂.det = 1 ∧ X₃.det = 1 ∧
          X₁ * Y₁ = 1 ∧ X₂ * Y₂ = 1 ∧ X₃ * Y₃ = 1 ∧ X₁ * A * X₁ᵀ = A ∧
          X₂ * (T * A) * X₂ᵀ = T * A ∧ X₃ * (U * A) * X₃ᵀ = U * A ∧
          ((X₁ * T * Y₁) * (X₂ * T * Y₂) * (X₃ * T * Y₃)) ^ 13 = 1 ∧
          (X₁ * T * Y₁) * (X₂ * T * Y₂) * (X₃ * T * Y₃) ≠ 1) :=
  ⟨fun _ _ _ hrep => c1_of ch260383_sym hrep,
    fun _ _ _ hrep => c2_of ch260383_inv ch260383_pairs hrep,
    fun _ _ _ hrep => c3_of ch260383_inv ch260383_sym ch260383_pairs ch260383_c3 hrep⟩

end Certificates
