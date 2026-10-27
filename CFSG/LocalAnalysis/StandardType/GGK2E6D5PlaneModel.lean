module

public import CFSG.LocalAnalysis.StandardType.GGKOnlyE6Normalization
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.SimpleRoots
public import CFSG.LocalAnalysis.StandardType.ZS.AdaptMonomial

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem d5_actual_CK_model
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ}
    {C : Matrix Λ Λ ℤ} (e : Fin 5 ≃ Λ)
    (hM : M = (ggCoxeterMatrixD 5).reindex e) (hC : GGIntCartan M C) :
    ∀ i j : Fin 5, C (e i) (e j) = CartanMatrix.D 5 i j := by
  classical
  have hMle : ∀ a b, M a b ≤ 3 := by
    intro a b
    rw [hM, CoxeterMatrix.reindex_apply, ggCoxeterMatrixD_apply]
    split_ifs <;> omega
  have hone : GGAtMostOneMultipleEdge M := by
    intro i j k l hij hkl h4 _
    have := hMle i j
    omega
  let Cstd : Matrix Λ Λ ℤ := Matrix.reindex e e (CartanMatrix.D 5)
  have hCstd : GGIntCartan M Cstd := by
    rw [hM]
    exact (ggIntCartan_D 5).reindex e
  have hEq := GGIntCartan.eq_or_eq_transpose hC hCstd hone
  intro i j
  rcases hEq with h | h
  · rw [h]
    simp [Cstd]
  · rw [h]
    simp [Cstd, Matrix.transpose_apply, (CartanMatrix.D_isSymm 5).apply]

end CFSG.StandardType

end
