module

public import CFSG.RankThree.PartTwo.Sec21.Item211Res6ProofFrame
public import CFSG.RankThree.PartTwo.Sec21.Item211Lie2ProofU42Char

public section

namespace CFSG.RankThree.PartTwo.Sec21

namespace Item211Res6Proof

open CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification
open Item211Lie2Proof
open scoped MatrixGroups Matrix

section BlockCommon

variable {K : Type} [Field K]

theorem sZero_sq : (sZero : SL(3, K)) ^ 2 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_sZero, Matrix.SpecialLinearGroup.coe_one,
    Matrix.diagonal_pow]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

theorem conj_injective_three : Function.Injective
    (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)) :=
  conj_injective' center_projectiveSL_three_eq_bot'

theorem commute_of_proj_commute_block (hK2 : (2 : K) ≠ 0) {Z W : SL(3, K)}
    (hZ : Z * sZero = sZero * Z) (hW : W * sZero = sZero * W)
    (h : proj 3 K Z * proj 3 K W = proj 3 K W * proj 3 K Z) :
    (Z : Matrix (Fin 3) (Fin 3) K) * W = (W : Matrix (Fin 3) (Fin 3) K) * Z := by
  obtain ⟨c, -, hc⟩ := exists_smul_of_proj_commute (Z := Z) (Y := W) h
  have e22 := congrFun (congrFun hc 2) 2
  rw [Matrix.smul_apply, apply_two_two_mul hK2 hZ hW, apply_two_two_mul hK2 hW hZ,
    smul_eq_mul] at e22
  have hc1 : c = 1 := by
    have h0 : (1 - c) * ((Z : Matrix (Fin 3) (Fin 3) K) 2 2 * (W : Matrix (Fin 3) (Fin 3) K) 2 2)
        = 0 := by linear_combination e22
    rcases mul_eq_zero.mp h0 with h' | h'
    · linear_combination -h'
    · exact absurd h' (mul_ne_zero (apply_two_two_ne_zero hK2 hZ) (apply_two_two_ne_zero hK2 hW))
  rw [hc1, one_smul] at hc
  rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul]
  exact hc

@[expose] def xZero : MulAut (projectiveSL 3 K) := MulAut.conj (proj 3 K sZero)

theorem apply_x0_of_mem {T : Subgroup (MulAut (projectiveSL 3 K))}
    (hXc : ∀ t ∈ T, t * xZero = xZero * t) {t : MulAut (projectiveSL 3 K)} (ht : t ∈ T) :
    t (proj 3 K sZero) = proj 3 K sZero := by
  apply conj_injective_three
  rw [← mul_conj_mul_inv']
  change t * xZero * t⁻¹ = xZero
  rw [hXc t ht, mul_inv_cancel_right]

theorem exists_block_of_mem {T : Subgroup (MulAut (projectiveSL 3 K))}
    (hX : xZero ∈ T) {c : MulAut (projectiveSL 3 K)}
    (hc : c ∈ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range ⊓
      Subgroup.centralizer (T : Set (MulAut (projectiveSL 3 K)))) :
    ∃ Z : SL(3, K), Z * sZero = sZero * Z ∧ c = MulAut.conj (proj 3 K Z) := by
  obtain ⟨⟨y, rfl⟩, hcT⟩ := Subgroup.mem_inf.mp hc
  obtain ⟨Z, rfl⟩ := proj_surjective 3 K y
  refine ⟨Z, ?_, rfl⟩
  have h1 := Subgroup.mem_centralizer_iff.mp hcT _ hX
  have h2 : proj 3 K Z * proj 3 K sZero = proj 3 K sZero * proj 3 K Z := by
    apply conj_injective_three
    rw [map_mul, map_mul]
    exact h1.symm
  have hc := CFSG.Quasithin.E22S.commute_of_proj_commute_two sZero_sq h2.symm
  exact hc.symm

theorem isBlockScalar_of_mem (hK2 : (2 : K) ≠ 0) {T : Subgroup (MulAut (projectiveSL 3 K))}
    (hX : xZero ∈ T) (hXc : ∀ t ∈ T, t * xZero = xZero * t)
    (hnab : ¬ (∀ a ∈ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range ⊓
        Subgroup.centralizer ((T ⊓ (MulAut.conj : projectiveSL 3 K →* MulAut
          (projectiveSL 3 K)).range : Subgroup (MulAut (projectiveSL 3 K))) :
            Set (MulAut (projectiveSL 3 K))),
      ∀ b ∈ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range ⊓
        Subgroup.centralizer ((T ⊓ (MulAut.conj : projectiveSL 3 K →* MulAut
          (projectiveSL 3 K)).range : Subgroup (MulAut (projectiveSL 3 K))) :
            Set (MulAut (projectiveSL 3 K))),
      a * b = b * a))
    {Yl : SL(3, K)} (hY : MulAut.conj (proj 3 K Yl) ∈ T) :
    IsBlockScalar (Yl : Matrix (Fin 3) (Fin 3) K) := by
  have hXI : xZero ∈ T ⊓ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range :=
    ⟨hX, ⟨_, rfl⟩⟩
  have hYI : MulAut.conj (proj 3 K Yl) ∈
      T ⊓ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range := ⟨hY, ⟨_, rfl⟩⟩
  have hYs : Yl * sZero = sZero * Yl := by
    have h1 := hXc _ hY
    have h2 : proj 3 K Yl * proj 3 K sZero = proj 3 K sZero * proj 3 K Yl := by
      apply conj_injective_three
      rw [map_mul, map_mul]
      exact h1
    exact (CFSG.Quasithin.E22S.commute_of_proj_commute_two sZero_sq h2.symm).symm
  have hYb := isBlock_coe hK2 hYs
  by_contra hns
  apply hnab
  have hcomm : ∀ c ∈ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range ⊓
      Subgroup.centralizer ((T ⊓ (MulAut.conj : projectiveSL 3 K →* MulAut
        (projectiveSL 3 K)).range : Subgroup (MulAut (projectiveSL 3 K))) :
          Set (MulAut (projectiveSL 3 K))),
      ∃ Z : SL(3, K), c = MulAut.conj (proj 3 K Z) ∧ Z * sZero = sZero * Z ∧
        (Yl : Matrix (Fin 3) (Fin 3) K) * Z = (Z : Matrix (Fin 3) (Fin 3) K) * Yl := by
    intro c hc
    obtain ⟨⟨y, rfl⟩, hcT⟩ := Subgroup.mem_inf.mp hc
    obtain ⟨Z, rfl⟩ := proj_surjective 3 K y
    have hZx : proj 3 K Z * proj 3 K sZero = proj 3 K sZero * proj 3 K Z := by
      apply conj_injective_three
      rw [map_mul, map_mul]
      exact (Subgroup.mem_centralizer_iff.mp hcT _ hXI).symm
    have hZs : Z * sZero = sZero * Z :=
      (CFSG.Quasithin.E22S.commute_of_proj_commute_two sZero_sq hZx.symm).symm
    have hZY : proj 3 K Yl * proj 3 K Z = proj 3 K Z * proj 3 K Yl := by
      apply conj_injective_three
      rw [map_mul, map_mul]
      exact Subgroup.mem_centralizer_iff.mp hcT _ hYI
    exact ⟨Z, rfl, hZs, commute_of_proj_commute_block hK2 hYs hZs hZY⟩
  intro a ha b hb
  obtain ⟨Z, rfl, hZs, hYZ⟩ := hcomm a ha
  obtain ⟨Z', rfl, hZ's, hYZ'⟩ := hcomm b hb
  have hZZ' := commute_of_commute_of_not_blockScalar hYb (isBlock_coe hK2 hZs)
    (isBlock_coe hK2 hZ's) hns hYZ hYZ'
  have h1 : Z * Z' = Z' * Z := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    exact hZZ')
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, h1]

theorem commute_of_isBlockScalar_of_isBlk {Z W : Matrix (Fin 3) (Fin 3) K}
    (hZ : IsBlockScalar Z) (hW : IsBlk W) : Z * W = W * Z := by
  obtain ⟨⟨a02, a12, a20, a21⟩, a01, a10, a00⟩ := hZ
  obtain ⟨b02, b12, b20, b21⟩ := hW
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, a02, a12, a20, a21, a01, a10, b02, b12, b20,
      b21, a00] <;> ring

theorem eq_one_or_eq_x0_of_blockScalar {Z : SL(3, K)}
    (hZ : IsBlockScalar (Z : Matrix (Fin 3) (Fin 3) K)) (h2 : proj 3 K Z ^ 2 = 1) :
    proj 3 K Z = 1 ∨ proj 3 K Z = proj 3 K sZero := by
  obtain ⟨⟨h02, h12, h20, h21⟩, h01, h10, h00⟩ := hZ
  rw [← map_pow, proj_eq_one_iff, mem_scalars] at h2
  obtain ⟨ζ, hζ3, hζ⟩ := h2
  have hsq : (Z : Matrix (Fin 3) (Fin 3) K) * Z = Matrix.scalar (Fin 3) (ζ : K) := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← pow_two, hζ]
  have e00 := congrFun (congrFun hsq 0) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_three, h01, h02, h10, h20, mul_zero,
    add_zero, Matrix.scalar_apply, Matrix.diagonal_apply_eq] at e00
  have hdet := Z.2
  rw [Matrix.det_fin_three, h01, h02, h10, h12, h20, h21, ← h00] at hdet
  simp only [mul_zero, zero_mul, sub_zero, add_zero] at hdet
  have hζ3' : (ζ : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hζ3, Units.val_one]
  have hb' : (Z : Matrix (Fin 3) (Fin 3) K) 2 2 = (ζ : K) ^ 2 := by
    have h2 : (ζ : K) * (Z : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
      rw [← e00]; linear_combination hdet
    linear_combination (ζ : K) ^ 2 * h2 - (Z : Matrix (Fin 3) (Fin 3) K) 2 2 * hζ3'
  have haζ : ((Z : Matrix (Fin 3) (Fin 3) K) 0 0 * ζ - 1) *
      ((Z : Matrix (Fin 3) (Fin 3) K) 0 0 * ζ + 1) = 0 := by
    have : ((Z : Matrix (Fin 3) (Fin 3) K) 0 0 * ζ - 1) *
        ((Z : Matrix (Fin 3) (Fin 3) K) 0 0 * ζ + 1) =
        ((Z : Matrix (Fin 3) (Fin 3) K) 0 0 * (Z : Matrix (Fin 3) (Fin 3) K) 0 0) *
          (ζ : K) ^ 2 - 1 := by ring
    rw [this, e00]
    linear_combination hζ3'
  rcases mul_eq_zero.mp haζ with h | h
  · left
    have ha' : (Z : Matrix (Fin 3) (Fin 3) K) 0 0 = (ζ : K) ^ 2 := by
      linear_combination (ζ : K) ^ 2 * h - (Z : Matrix (Fin 3) (Fin 3) K) 0 0 * hζ3'
    have ha'' : (Z : Matrix (Fin 3) (Fin 3) K) 1 1 = (ζ : K) ^ 2 := by rw [← h00, ha']
    rw [proj_eq_one_iff, mem_scalars]
    refine ⟨ζ ^ 2, by rw [← pow_mul, show 2 * 3 = 3 * 2 by rfl, pow_mul, hζ3, one_pow], ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.scalar_apply, Matrix.diagonal, h01, h02, h10, h20, h12, h21, ha', ha'', hb']
  · right
    have ha' : (Z : Matrix (Fin 3) (Fin 3) K) 0 0 = -(ζ : K) ^ 2 := by
      linear_combination (ζ : K) ^ 2 * h - (Z : Matrix (Fin 3) (Fin 3) K) 0 0 * hζ3'
    have ha'' : (Z : Matrix (Fin 3) (Fin 3) K) 1 1 = -(ζ : K) ^ 2 := by rw [← h00, ha']
    refine Item211Lie2Proof.proj_eq_proj_iff.mpr ⟨(ζ : K), hζ3', ?_⟩
    rw [coe_sZero]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.diagonal, h01, h02, h10, h20, h12, h21, ha', ha'', hb'] <;>
      linear_combination -hζ3'

end BlockCommon

end Item211Res6Proof

end CFSG.RankThree.PartTwo.Sec21
