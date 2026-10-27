module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UGram
public import CFSG.LieType.Chevalley.LangRootArithmeticDet

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open scoped Matrix

theorem e6_iform_self : ∀ x ∈ rootFinset .E6, iform x x = 2 := by
  decide +kernel

section Disc

theorem e6_gram_false
    {α β γ α' β' γ' : Fin Tag.E6.rank → ℤ}
    (hα : iform α α = 2) (hβ : iform β β = 2) (hγ : iform γ γ = 2)
    (hα' : iform α' α' = 2) (hβ' : iform β' β' = 2) (hγ' : iform γ' γ' = 2)
    (h1 : iform α' β' = iform α β) (h2 : iform α' γ' = iform α γ)
    (h3 : iform β' γ' = iform β γ)
    (hx1 : iform α α' = 0) (hx2 : iform α β' = 0) (hx3 : iform α γ' = 0)
    (hx4 : iform β α' = 0) (hx5 : iform β β' = 0) (hx6 : iform β γ' = 0)
    (hx7 : iform γ α' = 0) (hx8 : iform γ β' = 0) (hx9 : iform γ γ' = 0)
    (hg : gramDet3 α β γ = 4) : False := by
  classical
  let u : Fin 3 ⊕ Fin 3 → (Fin Tag.E6.rank → ℤ) := Sum.elim ![α, β, γ] ![α', β', γ']
  let G3 : Matrix (Fin 3) (Fin 3) ℤ :=
    !![2, iform α β, iform α γ; iform α β, 2, iform β γ; iform α γ, iform β γ, 2]
  have hG3 : G3.det = 4 := by
    rw [← hg]
    simp only [G3, Matrix.det_fin_three, gramDet3]
    simp
    ring
  have hy1 : iform α' α = 0 := by rw [iform_comm]; exact hx1
  have hy2 : iform β' α = 0 := by rw [iform_comm]; exact hx2
  have hy3 : iform γ' α = 0 := by rw [iform_comm]; exact hx3
  have hy4 : iform α' β = 0 := by rw [iform_comm]; exact hx4
  have hy5 : iform β' β = 0 := by rw [iform_comm]; exact hx5
  have hy6 : iform γ' β = 0 := by rw [iform_comm]; exact hx6
  have hy7 : iform α' γ = 0 := by rw [iform_comm]; exact hx7
  have hy8 : iform β' γ = 0 := by rw [iform_comm]; exact hx8
  have hy9 : iform γ' γ = 0 := by rw [iform_comm]; exact hx9
  have hc1 : iform β α = iform α β := iform_comm _ _
  have hc2 : iform γ α = iform α γ := iform_comm _ _
  have hc3 : iform γ β = iform β γ := iform_comm _ _
  have hc1' : iform β' α' = iform α β := by rw [iform_comm, h1]
  have hc2' : iform γ' α' = iform α γ := by rw [iform_comm, h2]
  have hc3' : iform γ' β' = iform β γ := by rw [iform_comm, h3]
  have hgram : ∀ i j, iform (u i) (u j) = (Matrix.fromBlocks G3 0 0 G3) i j := by
    rintro (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [u, G3, Matrix.fromBlocks, hα, hβ, hγ, hα', hβ', hγ', h1, h2, h3, hx1, hx2, hx3, hx4,
        hx5, hx6, hx7, hx8, hx9, hy1, hy2, hy3, hy4, hy5, hy6, hy7, hy8, hy9, hc1, hc2, hc3,
        hc1', hc2', hc3']
  let e : Fin 3 ⊕ Fin 3 ≃ Fin Tag.E6.rank := finSumFinEquiv
  let M : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ := Matrix.of fun k j => u (e.symm j) k
  have hsym : ∀ k l, Tag.E6.symmetrizedCartan k l = Tag.E6.cartan k l := by
    intro k l
    rw [symmetrizedCartan_apply]
    have : Tag.E6.symmetrizer k k = 1 := by fin_cases k <;> rfl
    rw [this, one_mul]
  have hMat : Mᵀ * Tag.E6.cartan * M =
      (Matrix.fromBlocks G3 0 0 G3).submatrix e.symm e.symm := by
    ext i j
    rw [Matrix.submatrix_apply, ← hgram]
    simp only [iform, Matrix.mul_apply, Matrix.transpose_apply, M, Matrix.of_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    rw [hsym]
  have hdet : (Mᵀ * Tag.E6.cartan * M).det = 16 := by
    rw [hMat, Matrix.det_submatrix_equiv_self e.symm, Matrix.det_fromBlocks_zero₂₁, hG3]
    norm_num
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_cartan_E6] at hdet
  have : M.det * 3 * M.det = 3 * (M.det * M.det) := by ring
  omega

end Disc

end CFSG.StandardType.TableCRes
