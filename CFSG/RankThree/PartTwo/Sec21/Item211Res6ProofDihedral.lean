module

public import CFSG.RankThree.PartTwo.Sec21.Item211Res6ProofBasics
public import CFSG.RankThree.PartTwo.Sec21.Item211Res6ProofFrame

public section

namespace CFSG.RankThree.PartTwo.Sec21

namespace Item211Res6Proof

open CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification
open Item211Lie2Proof Item211Res5Proof
open scoped MatrixGroups Matrix

section Dihedral

variable {K : Type} [Field K]

theorem commute_of_mem_closure {M : Type*} [Group M] {S : Set M}
    (h : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) :
    ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, x * y = y * x := by
  have h1 : Subgroup.closure S ≤ Subgroup.centralizer S := by
    rw [Subgroup.closure_le]
    intro a ha
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro b hb
    exact h b hb a ha
  have h2 : Subgroup.closure S ≤ Subgroup.centralizer (Subgroup.closure S : Set M) := by
    rw [Subgroup.closure_le]
    intro a ha
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro b hb
    exact (Subgroup.mem_centralizer_iff.mp (h1 hb) a ha).symm
  intro x hx y hy
  exact (Subgroup.mem_centralizer_iff.mp (h2 hy) x hx)

theorem isCyclic_of_comm_unique {M : Type*} [Group M] {P : Subgroup M} [Finite P]
    (hcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hP2 : IsPGroup 2 P)
    (h1 : ∀ a ∈ P, ∀ b ∈ P, a ^ 2 = 1 → b ^ 2 = 1 → a ≠ 1 → b ≠ 1 → a = b) : IsCyclic P := by
  let _ : CommGroup P :=
    { (inferInstance : Group P) with
      mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
  refine isCyclic_of_unique_involution hP2 fun a b ha hb ha1 hb1 => Subtype.ext ?_
  refine h1 a a.2 b b.2 ?_ ?_ ?_ ?_
  · simpa using congrArg Subtype.val ha
  · simpa using congrArg Subtype.val hb
  · exact fun h => ha1 (Subtype.ext h)
  · exact fun h => hb1 (Subtype.ext h)

theorem commute_of_commute_nonscalar {E X Y : Matrix (Fin 2) (Fin 2) K}
    (hE : ¬ ∃ c : K, E = c • (1 : Matrix (Fin 2) (Fin 2) K)) (hX : X * E = E * X)
    (hY : Y * E = E * Y) : X * Y = Y * X := by
  have hns : ¬ IsBlockScalar (blockMat E) := by
    rintro ⟨-, h01, h10, h00⟩
    apply hE
    refine ⟨E 0 0, ?_⟩
    simp only [blockMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at h01 h10 h00
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, h10, h00]
  have h := commute_of_commute_of_not_blockScalar (isBlock_blockMat E) (isBlock_blockMat X)
    (isBlock_blockMat Y) hns (by rw [← blockMat_mul, ← blockMat_mul, hX])
    (by rw [← blockMat_mul, ← blockMat_mul, hY])
  rw [← blockMat_mul, ← blockMat_mul] at h
  have := congrArg upper h
  rwa [upper_blockMat, upper_blockMat] at this

theorem eq_one_or_neg_of_sq (hK2 : (2 : K) ≠ 0) {M : Matrix (Fin 2) (Fin 2) K}
    (h2 : M * M = 1) (hdet : M.det = 1) : M = 1 ∨ M = -1 := by
  have e00 := congrFun (congrFun h2 0) 0
  have e01 := congrFun (congrFun h2 0) 1
  have e10 := congrFun (congrFun h2 1) 0
  have e11 := congrFun (congrFun h2 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq] at e00 e11
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by
    decide), Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at e01 e10
  rw [Matrix.det_fin_two] at hdet
  have htr : (M 0 0 + M 1 1) ^ 2 = 4 := by linear_combination e00 + e11 + 2 * hdet
  have htr0 : M 0 0 + M 1 1 ≠ 0 := by
    intro h0
    rw [h0] at htr
    have h4 : (4 : K) = 2 * 2 := by norm_num
    rw [h4] at htr
    exact mul_ne_zero hK2 hK2 (by linear_combination -htr)
  have h01 : M 0 1 = 0 := by
    have : M 0 1 * (M 0 0 + M 1 1) = 0 := by linear_combination e01
    exact (mul_eq_zero.mp this).resolve_right htr0
  have h10 : M 1 0 = 0 := by
    have : M 1 0 * (M 0 0 + M 1 1) = 0 := by linear_combination e10
    exact (mul_eq_zero.mp this).resolve_right htr0
  simp only [h01, h10, mul_zero, add_zero, zero_add, sub_zero] at e00 e11 hdet
  have hd : M 0 0 = M 1 1 := by
    have h1 : M 0 0 * (M 0 0 - M 1 1) = 0 := by linear_combination e00 - hdet
    rcases mul_eq_zero.mp h1 with h | h
    · rw [h, zero_mul] at e00; exact absurd e00 zero_ne_one
    · linear_combination h
  rcases mul_self_eq_one_iff.mp e00 with h | h
  · left
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, h10, h, ← hd]
  · right
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, h10, h, ← hd]

theorem adjugate_transpose_block {Z : Matrix (Fin 3) (Fin 3) K} (hZ : IsBlk Z) :
    (Z.adjugate)ᵀ = !![Z 2 2 * Z 1 1, -(Z 2 2 * Z 1 0), 0; -(Z 2 2 * Z 0 1), Z 2 2 * Z 0 0, 0;
      0, 0, Z 0 0 * Z 1 1 - Z 0 1 * Z 1 0] := by
  obtain ⟨h02, h12, h20, h21⟩ := hZ
  rw [Matrix.adjugate_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h02, h12, h20, h21] <;> ring

theorem upper_mul_eq_cube_smul {Z g : Matrix (Fin 3) (Fin 3) K} (hZ : IsBlk Z) (hg : IsBlk g)
    (hdet : Z.det = 1) (hg22 : g 2 2 ≠ 0) {η : K}
    (h : Z * g = η • (g * (Z.adjugate)ᵀ)) :
    upper Z * (upper g * (jTwo : GL (Fin 2) K).val) =
      (Z 2 2) ^ 3 • ((upper g * (jTwo : GL (Fin 2) K).val) * upper Z) := by
  obtain ⟨z02, z12, z20, z21⟩ := hZ
  obtain ⟨g02, g12, g20, g21⟩ := hg
  rw [adjugate_transpose_block ⟨z02, z12, z20, z21⟩] at h
  rw [det_of_isBlock ⟨z02, z12, z20, z21⟩] at hdet
  have e : ∀ i j, (Z * g) i j = (η • (g * !![Z 2 2 * Z 1 1, -(Z 2 2 * Z 1 0), 0;
      -(Z 2 2 * Z 0 1), Z 2 2 * Z 0 0, 0; 0, 0, Z 0 0 * Z 1 1 - Z 0 1 * Z 1 0])) i j :=
    fun i j => by rw [h]
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  have e22 := e 2 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, z02, z12, z20, z21, g02, g12, g20,
    g21] at e00 e01 e10 e11 e22
  have hη : η = Z 2 2 ^ 2 := by
    have h1 : Z 2 2 = η * (Z 0 0 * Z 1 1 - Z 0 1 * Z 1 0) := by
      have : (Z 2 2 - η * (Z 0 0 * Z 1 1 - Z 0 1 * Z 1 0)) * g 2 2 = 0 := by
        linear_combination e22
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hg22)
    linear_combination -(Z 2 2) * h1 - η * hdet
  subst hη
  rw [coe_jTwo]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, upper] <;>
    first | linear_combination e00 | linear_combination -e00 | linear_combination e01 |
      linear_combination -e01 | linear_combination e10 | linear_combination -e10 |
      linear_combination e11 | linear_combination -e11

theorem commute_of_upper_commute {Z W : Matrix (Fin 3) (Fin 3) K} (hZ : IsBlk Z) (hW : IsBlk W)
    (h : upper Z * upper W = upper W * upper Z) : Z * W = W * Z := by
  obtain ⟨z02, z12, z20, z21⟩ := hZ
  obtain ⟨w02, w12, w20, w21⟩ := hW
  have e : ∀ i j, (upper Z * upper W) i j = (upper W * upper Z) i j := fun i j => by rw [h]
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  simp only [upper, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one] at e00 e01 e10 e11
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, z02, z12, z20, z21, w02, w12, w20, w21] <;>
    first | linear_combination e00 | linear_combination e01 | linear_combination e10 |
      linear_combination e11 | ring

theorem det_upper_mul_two_two (hK2 : (2 : K) ≠ 0) {Z : SL(3, K)} (hZ : Z * sZero = sZero * Z) :
    (upper (Z : Matrix (Fin 3) (Fin 3) K)).det * (Z : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
  rw [← det_eq_det_upper (isBlock_coe hK2 hZ)]
  exact Z.2

theorem upper_mul_eq_of_fixed (hK2 : (2 : K) ≠ 0) {g : GL (Fin 3) K}
    (hg : IsBlk (g : Matrix (Fin 3) (Fin 3) K)) {Z : SL(3, K)} (hZ : Z * sZero = sZero * Z)
    (hfix : (conjAut 3 K g * dualAut 3 K) (proj 3 K Z) = proj 3 K Z) :
    upper (Z : Matrix (Fin 3) (Fin 3) K) * (upper (g : Matrix (Fin 3) (Fin 3) K) *
        (jTwo : GL (Fin 2) K).val) = ((Z : Matrix (Fin 3) (Fin 3) K) 2 2) ^ 3 •
      ((upper (g : Matrix (Fin 3) (Fin 3) K) * (jTwo : GL (Fin 2) K).val) *
        upper (Z : Matrix (Fin 3) (Fin 3) K)) := by
  rw [MulAut.mul_apply, dualAut_proj, conjAut_proj] at hfix
  obtain ⟨η, -, hη⟩ := Item211Lie2Proof.proj_eq_proj_iff.mp hfix
  rw [coe_slConjugation] at hη
  have hg22 : (g : Matrix (Fin 3) (Fin 3) K) 2 2 ≠ 0 := by
    intro h0
    have := (Matrix.isUnits_det_units g).ne_zero
    rw [det_eq_det_upper hg, h0, mul_zero] at this
    exact this rfl
  refine upper_mul_eq_cube_smul (isBlock_coe hK2 hZ) hg Z.2 hg22 (η := η) ?_
  have e : ((Z⁻¹ : SL(3, K)).transpose : Matrix (Fin 3) (Fin 3) K) =
      ((Z : Matrix (Fin 3) (Fin 3) K).adjugate)ᵀ := by
    change (((Z⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K))ᵀ = _
    rw [Matrix.SpecialLinearGroup.coe_inv]
  rw [e] at hη
  calc (Z : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K)
      = (η • ((g : Matrix (Fin 3) (Fin 3) K) * ((Z : Matrix (Fin 3) (Fin 3) K).adjugate)ᵀ *
          ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))) * (g : Matrix (Fin 3) (Fin 3) K) := by
        rw [← hη]
    _ = _ := by
        rw [Matrix.smul_mul,
          Matrix.mul_assoc _ ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K),
          ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]

end Dihedral

end Item211Res6Proof

end CFSG.RankThree.PartTwo.Sec21
