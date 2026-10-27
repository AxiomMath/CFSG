module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieSylA
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieSylC
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieSylD

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.L5

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.U5K.Hyp
  CFSG.LocalAnalysis.EvenBN.U5 CFSG.LocalAnalysis.ComponentInitial

section General

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem syl_mat_levHom (B : SpecialLinearGroup (Fin 2) h.fixedField) :
    mat (levHom h B) = oddDiag h (slM B) 1 := by
  rw [levHom_eq_lev, mat_lev, det_slM, map_one, div_one]

theorem syl_barInvT_smul {c : K} (hc : c ≠ 0) {M : Matrix (Fin 2) (Fin 2) K}
    (hM : IsUnit M.det) : barInvT h (c • M) = (h.bar c)⁻¹ • barInvT h M := by
  symm
  apply eq_barInvT_of_mul_eq_one
  have : ((c • M).map h.bar)ᵀ = h.bar c • (M.map h.bar)ᵀ := by
    ext i j
    simp
  rw [this, smul_mul_assoc, mul_smul_comm, conjTranspose_mul_barInvT hM, smul_smul,
    mul_inv_cancel₀ ((map_ne_zero h.bar).2 hc), one_smul]

theorem syl_oddDiag_smul {lam : K} (hl : lam * h.bar lam = 1) {M : Matrix (Fin 2) (Fin 2) K}
    (hM : IsUnit M.det) : oddDiag h (lam • M) lam = lam • oddDiag h M 1 := by
  have hl0 : lam ≠ 0 := left_ne_zero_of_mul_eq_one hl
  have hb : (h.bar lam)⁻¹ = lam := inv_eq_of_mul_eq_one_left hl
  rw [oddDiag, oddDiag, syl_barInvT_smul hl0 hM, hb]
  ext a b
  rcases a with i | k | i <;> rcases b with j | l | j <;> simp

theorem syl_proj_eq_of_smul {u g : hypSU h 2 1} {lam : K} (hl : lam * h.bar lam = 1)
    (hl5 : lam ^ 5 = 1) (hg : mat g = lam • mat u) :
    hypProj h 2 1 g = hypProj h 2 1 u := by
  have hl0 : lam ≠ 0 := left_ne_zero_of_mul_eq_one hl
  have hmem : u⁻¹ * g ∈ hypScalars h 2 1 := by
    refine ⟨Units.mk0 lam hl0, hl, ?_, ?_⟩
    · apply Units.ext
      simpa using hl5
    · apply Units.ext
      rw [GeneralLinearGroup.coe_scalar]
      change mat (u⁻¹ * g) = _
      rw [mat_mul, hg, Matrix.mul_smul, ← mat_mul, inv_mul_cancel, mat_one]
      simp [Matrix.smul_one_eq_diagonal]
  exact (QuotientGroup.eq.mpr hmem).symm

end General

variable {K : Type} [Field K]

theorem syl_cent_decomp (h : UnitaryFieldData 2 2 K) {x : hypPSU h 2 1}
    (hx : x ∈ Subgroup.centralizer ({t5Y h} : Set (hypPSU h 2 1))) :
    ∃ B : SpecialLinearGroup (Fin 2) h.fixedField, ∃ s ∈ Ssub h,
      x = hypProj h 2 1 (levHom h B * s) := by
  obtain ⟨g, rfl⟩ := hypProj_surjective h 2 1 x
  obtain ⟨A, C, x', d, hAu, hC, hd, -, hAJ, hmat⟩ :=
    syl_decomp_of_comm ((syl_mem_centralizer_iff g).1 hx)
  obtain ⟨lam, B, hl, hAB⟩ := syl_scalar_decomp hAJ
  obtain ⟨s, hs, hsm⟩ := exists_mem_Ssub (hK := h) hC
  refine ⟨B, s, hs, ?_⟩
  have hl0 : lam ≠ 0 := left_ne_zero_of_mul_eq_one hl
  have hl5 : lam ^ 5 = 1 := by
    have hb : h.bar lam = lam ^ 4 := by rw [h.bar_apply]; norm_num
    rw [hb] at hl
    linear_combination hl
  have hdet : A.det = lam * lam := by
    rw [hAB, Matrix.det_smul, det_slM]
    simp [sq]
  have hd' : d = lam := by
    rw [hd, hdet, map_mul, h.bar_apply]
    field_simp
    linear_combination lam ^ 3 * hl5
  refine syl_proj_eq_of_smul hl hl5 ?_
  rw [mat_mul, syl_mat_levHom, hsm, hmat, hd', hAB, syl_oddDiag_smul hl (isUnit_det_slM B),
    Matrix.smul_mul]

end CFSG.Quasithin.H13.F431.Un.L5
