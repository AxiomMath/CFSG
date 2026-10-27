module

public import Certificates.Certificate799700

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.GL6

open Matrix

private theorem fm_J0_transpose : J0ᵀ = J0 := by decide

private theorem fm_alt_sum (a b c d e f : ZMod 2) :
    a * d + d * a + b * e + e * b + c * f + f * c = 0 := by
  revert a b c d e f
  decide

private theorem fm_diag_zero (M : Matrix (Fin 6) (Fin 6) (ZMod 2)) (i : Fin 6) :
    (Mᵀ * J0 * M) i i = 0 := by
  have key := fm_alt_sum (M 0 i) (M 1 i) (M 2 i) (M 3 i) (M 4 i) (M 5 i)
  simp [Matrix.mul_apply, Fin.sum_univ_six, J0]
  linear_combination key

private theorem fm_conj_mem (H Hi W J Q : Matrix (Fin 6) (Fin 6) (ZMod 2))
    (hHi : H * Hi = 1) (hQ : Hᵀ * J * H = Q) (hW : Wᵀ * Q * W = Q) :
    (H * W * Hi)ᵀ * J * (H * W * Hi) = J := by
  have h1 : Hiᵀ * Hᵀ = 1 := by rw [← Matrix.transpose_mul, hHi, Matrix.transpose_one]
  calc (H * W * Hi)ᵀ * J * (H * W * Hi)
      = Hiᵀ * (Wᵀ * (Hᵀ * J * H) * W) * Hi := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = Hiᵀ * (Wᵀ * Q * W) * Hi := by rw [hQ]
    _ = Hiᵀ * Q * Hi := by rw [hW]
    _ = Hiᵀ * (Hᵀ * J * H) * Hi := by rw [hQ]
    _ = (Hiᵀ * Hᵀ) * J * (H * Hi) := by simp only [Matrix.mul_assoc]
    _ = J := by rw [h1, hHi, Matrix.one_mul, Matrix.mul_one]

private theorem fm_exists_witness
    (P : Matrix (Fin 6) (Fin 6) (ZMod 2)) (hsym : Pᵀ = P) (hdiag : ∀ i, P i i = 0)
    (hne : P ≠ J0) :
    ∃ s w : G6, s ∈ Sp0 ∧ w * u0 = u0 * w ∧ w ∉ Sp0 ∧
      (w : Matrix (Fin 6) (Fin 6) (ZMod 2))ᵀ *
          ((s : Matrix (Fin 6) (Fin 6) (ZMod 2))ᵀ * P * (s : Matrix (Fin 6) (Fin 6) (ZMod 2))) *
          (w : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
        (s : Matrix (Fin 6) (Fin 6) (ZMod 2))ᵀ * P * (s : Matrix (Fin 6) (Fin 6) (ZMod 2)) :=
  Certificates.certificate799700 P hsym hdiag hne

theorem eq_sp0_of_le (X : Subgroup G6)
    (hX : X ⊓ Subgroup.centralizer {u0} = K0) (hK0 : K0 ≤ Sp0) (hle : Sp0 ≤ X) : X = Sp0 := by
  refine le_antisymm ?_ hle
  intro g hg
  by_contra hgS
  have hne : (g : Matrix (Fin 6) (Fin 6) (ZMod 2))ᵀ * J0 *
      (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) ≠ J0 := fun h => hgS h
  have hsym : ((g : Matrix (Fin 6) (Fin 6) (ZMod 2))ᵀ * J0 *
      (g : Matrix (Fin 6) (Fin 6) (ZMod 2)))ᵀ =
      (g : Matrix (Fin 6) (Fin 6) (ZMod 2))ᵀ * J0 * (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, fm_J0_transpose,
      Matrix.mul_assoc]
  obtain ⟨s, w, hs, hwu, hwS, hkey⟩ :=
    fm_exists_witness ((g : Matrix (Fin 6) (Fin 6) (ZMod 2))ᵀ * J0 *
      (g : Matrix (Fin 6) (Fin 6) (ZMod 2))) hsym (fm_diag_zero _) hne
  have hgs : g * s ∈ X := X.mul_mem hg (hle hs)
  have hQ : ((g * s : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2))ᵀ * J0 *
      ((g * s : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
      (s : Matrix (Fin 6) (Fin 6) (ZMod 2))ᵀ *
        ((g : Matrix (Fin 6) (Fin 6) (ZMod 2))ᵀ * J0 * (g : Matrix (Fin 6) (Fin 6) (ZMod 2))) *
        (s : Matrix (Fin 6) (Fin 6) (ZMod 2)) := by
    rw [Units.val_mul]
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  have hHi : ((g * s : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *
      (((g * s)⁻¹ : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hcS : g * s * w * (g * s)⁻¹ ∈ Sp0 := by
    show (((g * s * w * (g * s)⁻¹ : G6)) : Matrix (Fin 6) (Fin 6) (ZMod 2))ᵀ * J0 *
      ((g * s * w * (g * s)⁻¹ : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = J0
    rw [Units.val_mul, Units.val_mul]
    exact fm_conj_mem _ _ _ _ _ hHi hQ hkey
  have hcX : g * s * w * (g * s)⁻¹ ∈ X := hle hcS
  have hwX : w ∈ X := by
    have h3 := X.mul_mem (X.mul_mem (X.inv_mem hgs) hcX) hgs
    have e : (g * s)⁻¹ * (g * s * w * (g * s)⁻¹) * (g * s) = w := by group
    rwa [e] at h3
  have hwC : w ∈ Subgroup.centralizer {u0} := Subgroup.mem_centralizer_singleton_iff.mpr hwu
  have hwK : w ∈ K0 := by
    rw [← hX]
    exact Subgroup.mem_inf.mpr ⟨hwX, hwC⟩
  exact hwS (hK0 hwK)

end CFSG.RankThree.PartTwo.Sec21.FF81.GL6
