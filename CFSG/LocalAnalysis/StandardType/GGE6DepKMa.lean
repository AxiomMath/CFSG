module

public import CFSG.LocalAnalysis.StandardType.GGE6DepKGlueDefs
public import CFSG.LocalAnalysis.StandardType.GGE6DepModelShapeDefs
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Abel
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

public section

namespace CFSG.StandardType

namespace E6Dep

open Matrix

private lemma reflNorm_eq (d : Vec6) :
    reflNorm d = 1 + vecMulVec d (gram6.mulVec d) := by
  unfold reflNorm reflMat
  rw [Matrix.vecMulVec_smul]
  have h2 : (2 : ZMod 3) = -1 := by decide
  rw [h2, neg_one_smul, sub_neg_eq_add]

private lemma vecMulVec_mul_transpose (u v : Vec6) (M : Mat6) :
    vecMulVec u v * M = vecMulVec u (Mᵀ.mulVec v) := by
  rw [Matrix.vecMulVec_mul, ← Matrix.mulVec_transpose]

private lemma vecMulVec_mulVec' (u v w : Vec6) :
    (vecMulVec u v).mulVec w = (v ⬝ᵥ w) • u := by
  rw [Matrix.vecMulVec_mulVec]
  ext i
  simp [MulOpposite.smul_eq_mul_unop, smul_eq_mul, mul_comm]

private lemma dot_a (M : Mat6) (d v : Vec6) :
    (Mᵀ.mulVec (gram6.mulVec d)) ⬝ᵥ v = bil6 (M.mulVec v) d := by
  calc (Mᵀ.mulVec (gram6.mulVec d)) ⬝ᵥ v
      = v ⬝ᵥ (Mᵀ.mulVec (gram6.mulVec d)) := dotProduct_comm _ _
    _ = (gram6.mulVec d) ⬝ᵥ (M.mulVec v) :=
        Matrix.dotProduct_transpose_mulVec M v (gram6.mulVec d)
    _ = (M.mulVec v) ⬝ᵥ (gram6.mulVec d) := dotProduct_comm _ _
    _ = bil6 (M.mulVec v) d := rfl

theorem refl_eq_rK {M Ma : Mat6} {c : ZMod 3} {d : Vec6}
    (hMy : M.mulVec (kY c) = 0) (hMker : ∀ v, M.mulVec v = 0 → ∃ j : ZMod 3, v = j • kY c)
    (hMonto : ∀ v : Vec6, v 5 = 0 → ∃ u, M.mulVec u = v)
    (hG : Mᵀ * gram6 * M = gbeta c)
    (hMa2 : Ma * Ma = 1) (hMay : Ma.mulVec (kY c) = kY c)
    (hd5 : d 5 = 0) (hd : norm6 d = 1) (hconj : M * Ma = reflNorm d * M) :
    ∃ h : Vec6, normK c h = 1 ∧ Ma = rK c h ∧ M.mulVec h = d := by
  obtain ⟨h₁, hh₁⟩ := hMonto d hd5
  set a : Vec6 := Mᵀ.mulVec (gram6.mulVec d) with ha_def
  have hstep2 : M * (Ma - 1) = vecMulVec d a := by
    have h1 : M * (Ma - 1) = M * Ma - M := by rw [Matrix.mul_sub, Matrix.mul_one]
    have h2 : M * Ma - M = (reflNorm d - 1) * M := by
      rw [hconj, Matrix.sub_mul, Matrix.one_mul]
    have h3 : reflNorm d - 1 = vecMulVec d (gram6.mulVec d) := by
      rw [reflNorm_eq]; abel
    rw [h1, h2, h3, vecMulVec_mul_transpose]
  set N' : Mat6 := (Ma - 1) - vecMulVec h₁ a with hN'_def
  have hMN' : M * N' = 0 := by
    rw [hN'_def, Matrix.mul_sub, hstep2, Matrix.mul_vecMulVec, hh₁, sub_self]
  have hcol : ∀ j : Fin 6, ∃ bj : ZMod 3, (fun i => N' i j) = bj • kY c := by
    intro j
    apply hMker
    ext i
    have h := congrFun (congrFun hMN' i) j
    simpa [Matrix.mul_apply, Matrix.mulVec_apply_eq_sum] using h
  choose b hb_coeff using hcol
  have hN' : N' = vecMulVec (kY c) b := by
    ext i j
    have h := congrFun (hb_coeff j) i
    simpa [Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using h
  have hMa_decomp : Ma = 1 + (vecMulVec h₁ a + vecMulVec (kY c) b) := by
    have hN'_eq : (Ma - 1) - vecMulVec h₁ a = vecMulVec (kY c) b := by
      rw [← hN'_def]; exact hN'
    have h2 : Ma - 1 = vecMulVec (kY c) b + vecMulVec h₁ a := sub_eq_iff_eq_add.mp hN'_eq
    have h3 : Ma = (vecMulVec (kY c) b + vecMulVec h₁ a) + 1 := sub_eq_iff_eq_add.mp h2
    rw [h3]; abel
  set N : Mat6 := vecMulVec h₁ a + vecMulVec (kY c) b with hN_def
  have hMaN : Ma = 1 + N := by rw [hMa_decomp]
  have ha_h₁ : a ⬝ᵥ h₁ = 1 := by
    rw [ha_def, dot_a, hh₁]
    simpa only [norm6] using hd
  have ha_y : a ⬝ᵥ kY c = 0 := by
    rw [ha_def, dot_a, hMy]
    simp [bil6]
  have hb_y : b ⬝ᵥ kY c = 0 := by
    have h2 := hMay
    rw [hMaN, hN_def] at h2
    rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.add_mulVec,
        vecMulVec_mulVec', vecMulVec_mulVec', ha_y, zero_smul, zero_add] at h2
    have h3 : (b ⬝ᵥ kY c) • kY c = 0 := by
      have hh : kY c + (b ⬝ᵥ kY c) • kY c = kY c + 0 := by simpa using h2
      exact add_left_cancel hh
    have h4 := congrFun h3 4
    simpa [Pi.smul_apply, smul_eq_mul, kY] using h4
  have hsq : (1 + N) * (1 + N) = 1 := by
    rw [← hMaN]; exact hMa2
  have hexp : (1 + N) * (1 + N) = 1 + (N + N) + N * N := by noncomm_ring
  have hcancel : (N + N) + N * N = 0 := by
    have hh : (1 : Mat6) + ((N + N) + N * N) = (1 : Mat6) + 0 := by
      have h := hsq
      rw [hexp] at h
      simpa [add_assoc] using h
    exact add_left_cancel hh
  have hNN : N * N = N := by
    have h2N : N + N = -N := by
      have h2 : (2 : ZMod 3) = -1 := by decide
      calc N + N = (2 : ZMod 3) • N := by rw [two_smul]
        _ = (-1 : ZMod 3) • N := by rw [h2]
        _ = -N := by rw [neg_one_smul]
    rw [h2N] at hcancel
    have hsub : N * N - N = 0 := by
      rw [sub_eq_neg_add]; exact hcancel
    exact sub_eq_zero.mp hsub
  have hNN_exp : N * N = vecMulVec h₁ a + (b ⬝ᵥ h₁) • vecMulVec (kY c) a := by
    rw [hN_def]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.vecMulVec_mul_vecMulVec,
      Matrix.vecMulVec_smul, ha_h₁, ha_y, hb_y, Matrix.vecMulVec_zero,
      one_smul, zero_smul, add_zero, zero_add]
  have hb_eq : vecMulVec (kY c) b = (b ⬝ᵥ h₁) • vecMulVec (kY c) a := by
    have h1 : N = vecMulVec h₁ a + (b ⬝ᵥ h₁) • vecMulVec (kY c) a := by
      rw [← hNN, hNN_exp]
    rw [hN_def] at h1
    exact add_left_cancel h1
  have hvec_b : vecMulVec (kY c) b = vecMulVec (kY c) ((b ⬝ᵥ h₁) • a) := by
    rw [hb_eq, Matrix.vecMulVec_smul]
  have hb_val : b = (b ⬝ᵥ h₁) • a := by
    funext j
    have h := congrFun (congrFun hvec_b 4) j
    simpa [Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, kY] using h
  have hMh : M.mulVec (h₁ + (b ⬝ᵥ h₁) • kY c) = d := by
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, hh₁, hMy, smul_zero, add_zero]
  have ha_gbeta : a = (gbeta c).mulVec (h₁ + (b ⬝ᵥ h₁) • kY c) := by
    rw [ha_def, ← hMh]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hG]
  have hMa_final : Ma = 1 + vecMulVec (h₁ + (b ⬝ᵥ h₁) • kY c) a := by
    rw [hMaN, hN_def, hvec_b, Matrix.vecMulVec_smul, Matrix.add_vecMulVec, Matrix.smul_vecMulVec]
  refine ⟨h₁ + (b ⬝ᵥ h₁) • kY c, ?_, ?_, hMh⟩
  · rw [normK, bilK, ← ha_gbeta]
    rw [dotProduct_comm, ha_def, dot_a, hMh]
    simpa only [norm6] using hd
  · rw [hMa_final, ha_gbeta, rK]

end E6Dep

end CFSG.StandardType

end
