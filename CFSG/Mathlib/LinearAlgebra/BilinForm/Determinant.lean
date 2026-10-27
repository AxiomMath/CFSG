module

public import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis
public import Mathlib.LinearAlgebra.Determinant

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen

theorem det_eq_one_of_isAlt {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {B : LinearMap.BilinForm K V} (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (f : V →ₗ[K] V) (hf : ∀ u v, B (f u) (f v) = B u v) : LinearMap.det f = 1 := by
  classical
  obtain ⟨m, b, hb⟩ := hB.exists_basis_toMatrix_eq_J hnd
  have hcomp : B.comp f f = B :=
    LinearMap.ext₂ fun u v => by rw [LinearMap.BilinForm.comp_apply, hf]
  have hM : LinearMap.toMatrix b b f ∈ Matrix.symplecticGroup (Fin m) K := by
    rw [SymplecticGroup.mem_iff']
    have h := LinearMap.BilinForm.toMatrix_comp b b B f f
    rw [hcomp, hb] at h
    exact h.symm
  rw [← LinearMap.det_toMatrix b]
  exact SymplecticGroup.det_eq_one hM

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen
