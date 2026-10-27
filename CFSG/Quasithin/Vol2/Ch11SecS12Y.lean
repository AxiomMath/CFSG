module

public import CFSG.Quasithin.Vol2.Ch11SecS12F
public import CFSG.Quasithin.Vol2.Ch11SecS12R

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.SL3Model
open Matrix
open scoped MatrixGroups

section Matrices

variable {F : Type} [Field F] [CharP F 2]

theorem trace_eq_one_of_cube {B : Matrix (Fin 2) (Fin 2) F} (hdet : B.det = 1)
    (h3 : B * B * B = 1) (h1 : B ≠ 1) : B 0 0 + B 1 1 = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [Matrix.det_fin_two] at hdet
  have e : ∀ i j, (B * B * B) i j = (1 : Matrix (Fin 2) (Fin 2) F) i j := fun i j => by rw [h3]
  have E00 := e 0 0
  have E01 := e 0 1
  have E10 := e 1 0
  have E11 := e 1 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at E00 E01 E10 E11
  set t := B 0 0 + B 1 1 with ht
  have hq : B 0 1 * (t ^ 2 - 1) = 0 := by
    rw [ht]
    linear_combination E01 + B 0 1 * hdet
  have hr : B 1 0 * (t ^ 2 - 1) = 0 := by
    rw [ht]
    linear_combination E10 + B 1 0 * hdet
  have hp : B 0 0 * (t ^ 2 - 1) - t = 1 := by
    rw [ht]
    linear_combination E00 + (B 1 1 + 2 * B 0 0) * hdet
  have hs : B 1 1 * (t ^ 2 - 1) - t = 1 := by
    rw [ht]
    linear_combination E11 + (B 0 0 + 2 * B 1 1) * hdet
  by_cases h0 : t ^ 2 - 1 = 0
  · have : (t - 1) ^ 2 = 0 := by linear_combination h0 - (t - 1) * h2
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    linear_combination this
  · exfalso
    have hq0 := (mul_eq_zero.mp hq).resolve_right h0
    have hr0 := (mul_eq_zero.mp hr).resolve_right h0
    have hps : B 0 0 = B 1 1 := by
      have : (B 0 0 - B 1 1) * (t ^ 2 - 1) = 0 := by linear_combination hp - hs
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right h0)
    have ht0 : t = 0 := by rw [ht, hps]; linear_combination B 1 1 * h2
    have hp1 : B 0 0 = 1 := by
      rw [ht0] at hp
      linear_combination -hp - h2
    apply h1
    ext i j
    fin_cases i <;> fin_cases j
    · exact hp1
    · exact hq0
    · exact hr0
    · simp only [Fin.mk_one, Fin.isValue, Matrix.one_apply_eq]
      rw [← hps, hp1]

theorem exists_eigen_of_stab0 {A : SL(3, F)} (hA : A ∈ stab0 F) (hA3 : A ^ 3 = 1) (hA1 : A ≠ 1)
    {μ : F} (hμ : μ ^ 2 + μ + 1 = 0) : ∃ w : Fin 3 → F, w ≠ 0 ∧ A • w = μ • w := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨h0, h1, h20⟩ := stab0_col hA
  have hdet := det_leviMat hA
  have hB3 : leviMat A.1 * leviMat A.1 * leviMat A.1 = 1 := by
    have e1 : leviMat (A * A * A).1 = leviMat A.1 * leviMat A.1 * leviMat A.1 := by
      rw [leviMat_mul (Subgroup.mul_mem _ hA hA), leviMat_mul hA]
    rw [← e1, show A * A * A = A ^ 3 by rw [pow_three, mul_assoc], hA3]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [leviMat]
  have hB1 : leviMat A.1 ≠ 1 := by
    intro hB
    have e11 : A.1 1 1 = 1 := by simpa [leviMat] using congrFun (congrFun hB 0) 0
    have e12 : A.1 1 2 = 0 := by simpa [leviMat] using congrFun (congrFun hB 0) 1
    have e21 : A.1 2 1 = 0 := by simpa [leviMat] using congrFun (congrFun hB 1) 0
    have e22 : A.1 2 2 = 1 := by simpa [leviMat] using congrFun (congrFun hB 1) 1
    have hsq : A ^ 2 = 1 := by
      apply Subtype.ext
      rw [show A ^ 2 = A * A from sq A, Matrix.SpecialLinearGroup.coe_mul]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three, h0, h1, h20, e11, e12, e21, e22]
      all_goals linear_combination (A.1 0 _) * h2
    exact hA1 (eq_one_of_sq_of_cube hsq hA3)
  have ht := trace_eq_one_of_cube hdet hB3 hB1
  simp only [leviMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at ht
  rw [leviMat, Matrix.det_fin_two_of] at hdet
  have hdet0 : (A.1 - μ • (1 : Matrix (Fin 3) (Fin 3) F)).det = 0 := by
    rw [Matrix.det_fin_three]
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
      Matrix.one_apply_ne (show (0 : Fin 3) ≠ 1 by decide),
      Matrix.one_apply_ne (show (0 : Fin 3) ≠ 2 by decide),
      Matrix.one_apply_ne (show (1 : Fin 3) ≠ 0 by decide),
      Matrix.one_apply_ne (show (1 : Fin 3) ≠ 2 by decide),
      Matrix.one_apply_ne (show (2 : Fin 3) ≠ 0 by decide),
      Matrix.one_apply_ne (show (2 : Fin 3) ≠ 1 by decide), h0, h1, h20]
    linear_combination (1 - μ) * hdet + (1 - μ) * hμ - (1 - μ) * μ * ht - (1 - μ) * μ * h2
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet0
  refine ⟨w, hw0, ?_⟩
  rw [Matrix.SpecialLinearGroup.smul_def]
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hw
  exact hw

end Matrices

section Group

variable {G : Type} [Group G] [Finite G] {n : ℕ} {L K V V₁ : Subgroup G}

theorem exists_fixed_of_mul (D : NatData3 n L K V V₁) (hV₁V : V₁ ≤ V) {a b : G} (ha : a ∈ L)
    (hb : b ∈ LOf L V₁) {c : GaloisField 2 n} (hc3 : c ^ 3 = 1)
    (hac : ∀ w : Fin 3 → GaloisField 2 n, D.θ ⟨a, ha⟩ • w = c • w) (hb3 : b ^ 3 = 1)
    (hb1 : D.θ ⟨b, NatData3'.lOf_le hb⟩ ≠ 1) :
    ∃ v ∈ V, v ≠ 1 ∧ (a * b) * v * (a * b)⁻¹ = v := by
  have hA : D.θ ⟨b, NatData3'.lOf_le hb⟩ ∈ stab0 (GaloisField 2 n) :=
    NatData3'.theta_mem_stab0 D hV₁V ⟨b, hb⟩
  have hA3 : D.θ ⟨b, NatData3'.lOf_le hb⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨b, NatData3'.lOf_le hb⟩ : ↥L) ^ 3 = 1 := Subtype.ext (by simpa using hb3)
    rw [this, map_one]
  have hc0 : c ≠ 0 := by
    rintro rfl
    norm_num at hc3
  obtain ⟨w, hw0, hw⟩ : ∃ w : Fin 3 → GaloisField 2 n, w ≠ 0 ∧
      D.θ ⟨b, NatData3'.lOf_le hb⟩ • w = c⁻¹ • w := by
    by_cases hc1 : c = 1
    · refine ⟨vE _ 0, fun h => ?_, ?_⟩
      · have := congrFun h 0
        simp at this
      · rw [hc1, inv_one, one_smul]
        exact hA
    · refine exists_eigen_of_stab0 hA hA3 hb1 ?_
      have h1 : c ^ 2 + c + 1 = 0 := by
        have : (c - 1) * (c ^ 2 + c + 1) = 0 := by linear_combination hc3
        exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hc1)
      field_simp
      linear_combination h1
  have hab : a * b ∈ L := L.mul_mem ha (NatData3'.lOf_le hb)
  have hθ : D.θ ⟨a * b, hab⟩ • w = w := by
    have e : (⟨a * b, hab⟩ : ↥L) = ⟨a, ha⟩ * ⟨b, NatData3'.lOf_le hb⟩ := rfl
    rw [e, map_mul, mul_smul, hw, smul_comm, hac, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  refine ⟨(D.ψ.symm (Multiplicative.ofAdd w) : G), (D.ψ.symm _).2, fun h1 => ?_, ?_⟩
  · have h2 : D.ψ.symm (Multiplicative.ofAdd w) = 1 := Subtype.ext h1
    rw [MulEquiv.symm_apply_eq, map_one] at h2
    exact hw0 (by simpa using congrArg Multiplicative.toAdd h2)
  · have heq := D.equiv ⟨a * b, hab⟩ (D.ψ.symm (Multiplicative.ofAdd w))
    rw [MulEquiv.apply_symm_apply, natAct3_apply, toAdd_ofAdd, hθ, ← MulEquiv.eq_symm_apply] at heq
    have := congrArg Subtype.val heq
    rwa [conjAct_coe_apply] at this

end Group

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12
