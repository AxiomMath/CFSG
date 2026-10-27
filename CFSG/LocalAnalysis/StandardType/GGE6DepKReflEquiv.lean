module

public import CFSG.LocalAnalysis.StandardType.GGE6DepKGlueDefs
public import CFSG.LocalAnalysis.StandardType.GGE6DepModelShapeDefs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

public section

namespace CFSG.StandardType

namespace E6Dep

open Matrix

private lemma zmod_refl_aux : ∀ a c d : ZMod 3, a - (2 * c) * d = a + c * d := by
  decide +kernel

private lemma zmod_ne_zero_sq : ∀ x : ZMod 3, x ≠ 0 → x * x = 1 := by
  decide +kernel

private lemma zmod_mul_right_cancel :
    ∀ a b x : ZMod 3, x ≠ 0 → a * x = b * x → a = b := by
  decide +kernel

private lemma reflNorm_mulVec (u v : Vec6) :
    (reflNorm v).mulVec u = u + bil6 u v • v := by
  simp only [reflNorm, reflMat, bil6, Matrix.sub_mulVec, Matrix.one_mulVec,
    Matrix.vecMulVec_mulVec, op_smul_eq_smul]
  rw [smul_dotProduct, dotProduct_comm]
  ext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact zmod_refl_aux (u i) (u ⬝ᵥ Matrix.mulVec gram6 v) (v i)

private lemma bil6_smul_left (a : ZMod 3) (u w : Vec6) :
    bil6 (a • u) w = a * bil6 u w := by
  simp only [bil6, smul_dotProduct, smul_eq_mul]

private lemma bil6_smul_right (b : ZMod 3) (u w : Vec6) :
    bil6 u (b • w) = b * bil6 u w := by
  simp only [bil6, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem refl_equivariance {M k : Mat6} {c : Vec6}
    (hMonto : ∀ v : Vec6, v 5 = 0 → ∃ u, M.mulVec u = v)
    (hc : norm6 c = 1) (hk : k ∈ refl36) (hconj : M * reflNorm c = k * M) :
    (∀ v, bil6 (M.mulVec v) (M.mulVec c) = bil6 v c) ∧ norm6 (M.mulVec c) = 1 ∧
      k = reflNorm (M.mulVec c) := by
  classical
  rw [refl36] at hk
  obtain ⟨d, hd, hdk⟩ := Finset.mem_image.mp hk
  rw [Finset.mem_filter] at hd
  obtain ⟨-, hd5, hdn⟩ := hd
  have hd_eq : k = reflNorm d := hdk.symm
  have hdn' : bil6 d d = 1 := hdn
  have hE : ∀ v : Vec6, bil6 v c • M.mulVec c = bil6 (M.mulVec v) d • d := by
    intro v
    have h := congrArg (fun A : Mat6 => A.mulVec v) hconj
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, reflNorm_mulVec, ← hdk, reflNorm_mulVec,
      Matrix.mulVec_add, Matrix.mulVec_smul] at h
    exact add_left_cancel h
  set lam : ZMod 3 := bil6 (M.mulVec c) d with hlam
  have hMc : M.mulVec c = lam • d := by
    have h := hE c
    rw [show bil6 c c = 1 from hc, one_smul] at h
    exact h
  have hdne : d ≠ 0 := by
    intro h0
    have hz : bil6 d d = 0 := by rw [h0]; simp [bil6]
    rw [hdn'] at hz
    exact one_ne_zero hz
  have hdi : ∃ i : Fin 6, d i ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hdne (funext h)
  obtain ⟨i, hi⟩ := hdi
  obtain ⟨u, hu⟩ := hMonto d hd5
  have hmul : bil6 u c * lam = 1 := by
    have h := hE u
    rw [hu, hMc, smul_smul, show bil6 d d = 1 from hdn', one_smul] at h
    have h' := congrArg (fun w : Vec6 => w i) h
    simp only [Pi.smul_apply, smul_eq_mul] at h'
    exact zmod_mul_right_cancel (bil6 u c * lam) 1 (d i) hi (by simpa using h')
  have hlam_ne : lam ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hmul
    exact one_ne_zero hmul.symm
  have hlam_sq : lam * lam = 1 := zmod_ne_zero_sq lam hlam_ne
  have hEq : ∀ v : Vec6, bil6 (M.mulVec v) d = bil6 v c * lam := by
    intro v
    have h := hE v
    rw [hMc, smul_smul] at h
    have h' := congrArg (fun w : Vec6 => w i) h
    simp only [Pi.smul_apply, smul_eq_mul] at h'
    exact (zmod_mul_right_cancel (bil6 v c * lam) (bil6 (M.mulVec v) d) (d i) hi h').symm
  have hconj1 : ∀ v, bil6 (M.mulVec v) (M.mulVec c) = bil6 v c := by
    intro v
    rw [hMc, bil6_smul_right, hEq v, mul_comm (bil6 v c) lam, ← mul_assoc, hlam_sq, one_mul]
  have hnorm : norm6 (M.mulVec c) = 1 := by
    change bil6 (M.mulVec c) (M.mulVec c) = 1
    rw [hMc, bil6_smul_left, bil6_smul_right, show bil6 d d = 1 from hdn', mul_one, hlam_sq]
  have hrefl : reflNorm (lam • d) = reflNorm d := by
    rw [Matrix.ext_iff_mulVec]
    intro x
    rw [reflNorm_mulVec, reflNorm_mulVec, bil6_smul_right, smul_smul, mul_assoc,
      mul_comm (bil6 x d) lam, ← mul_assoc, hlam_sq, one_mul]
  have hk_eq : k = reflNorm (M.mulVec c) := by
    rw [hd_eq, hMc]
    exact hrefl.symm
  exact ⟨hconj1, hnorm, hk_eq⟩

end E6Dep

end CFSG.StandardType

end
