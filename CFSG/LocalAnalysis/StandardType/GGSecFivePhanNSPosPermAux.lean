module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

open scoped MatrixGroups

theorem ggNSPosPA_permSU_mul_anti {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    (σ τ : Equiv.Perm (Fin n)) :
    (ggPermSU (K := K) (f := f) (σ * τ) : GL (Fin n) K) =
      (ggPermSU (K := K) (f := f) τ : GL (Fin n) K) *
        (ggPermSU (K := K) (f := f) σ : GL (Fin n) K) := by
  apply Units.ext
  ext i j
  simp only [Units.val_mul]
  change (σ * τ).permMatrix K i j = (τ.permMatrix K * σ.permMatrix K) i j
  rw [Matrix.permMatrix_mul]

theorem ggNSPosPA_permSU_mul_anti' {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    (σ τ : Equiv.Perm (Fin n)) :
    ggPermSU (K := K) (f := f) (σ * τ) =
      ggPermSU (K := K) (f := f) τ * ggPermSU (K := K) (f := f) σ :=
  Subtype.ext (ggNSPosPA_permSU_mul_anti (K := K) (f := f) σ τ)

end CFSG.StandardType

end
