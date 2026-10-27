module

public import CFSG.Milestones.ASVolI.F411.aSwL3Aut
public import CFSG.Quasithin.Vol2.Ch12Sec6P31WXCS
public import CFSG.Quasithin.Vol2.Ch12Sec6P31WXLieL2
public import CFSG.Quasithin.Vol2.Ch12Sec6P31WXL3NT

public section

namespace CFSG.Quasithin.H13.P31X

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Calculus

variable {K : Type} [Field K]

theorem l3r_inv_isUpper (A : GL (Fin 3) K)
    (hA : (A : Matrix (Fin 3) (Fin 3) K).IsUpperTriangular) :
    ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsUpperTriangular := by
  have h : (A : Matrix (Fin 3) (Fin 3) K) *
      ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := Units.mul_inv A
  haveI : Invertible (A : Matrix (Fin 3) (Fin 3) K) :=
    ⟨((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K), Units.inv_mul A, Units.mul_inv A⟩
  rw [← Matrix.inv_eq_right_inv h]
  exact Matrix.blockTriangular_inv_of_blockTriangular hA

theorem l3r_conj_diag (A : GL (Fin 3) K)
    (hA : (A : Matrix (Fin 3) (Fin 3) K).IsUpperTriangular)
    (N : Matrix (Fin 3) (Fin 3) K) (hN : N.IsUpperTriangular) (i : Fin 3) :
    ((A : Matrix (Fin 3) (Fin 3) K) * N *
      ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) i i = N i i := by
  have hAi := l3r_inv_isUpper A hA
  have hAB : (A : Matrix (Fin 3) (Fin 3) K) *
      ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := Units.mul_inv A
  have hAN : ((A : Matrix (Fin 3) (Fin 3) K) * N).IsUpperTriangular :=
    Matrix.BlockTriangular.mul hA hN
  have h3 : (A : Matrix (Fin 3) (Fin 3) K) i i *
      ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i i = 1 := by
    rw [← mul_apply_self_of_isUpperTriangular hA hAi i, hAB, one_apply_eq]
  rw [mul_apply_self_of_isUpperTriangular hAN hAi i, mul_apply_self_of_isUpperTriangular hA hN i]
  linear_combination N i i * h3

theorem l3r_diag_upper (v : Fin 3 → K) : (Matrix.diagonal v).IsUpperTriangular :=
  fun _ _ h => Matrix.diagonal_apply_ne v (ne_of_gt h)

theorem l3r_det_diag {M : Matrix.SpecialLinearGroup (Fin 3) K}
    (hM : (M : Matrix (Fin 3) (Fin 3) K).IsUpperTriangular) :
    (M : Matrix (Fin 3) (Fin 3) K) 0 0 * (M : Matrix (Fin 3) (Fin 3) K) 1 1 *
      (M : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
  have h := M.2
  rw [Matrix.det_of_isUpperTriangular hM, Fin.prod_univ_three] at h
  exact h

theorem l3r_pow_upper {M : Matrix (Fin 3) (Fin 3) K} (hM : M.IsUpperTriangular) (m : ℕ) :
    (M ^ m).IsUpperTriangular := by
  induction m with
  | zero => exact fun _ _ h => by rw [pow_zero]; exact Matrix.one_apply_ne (ne_of_gt h)
  | succ m ih => rw [pow_succ]; exact Matrix.BlockTriangular.mul ih hM

theorem l3r_pow_diag {M : Matrix (Fin 3) (Fin 3) K} (hM : M.IsUpperTriangular) (m : ℕ)
    (i : Fin 3) : (M ^ m) i i = M i i ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, mul_apply_self_of_isUpperTriangular (l3r_pow_upper hM m) hM i, ih, pow_succ]

theorem l3r_sl_pow_diag {g : Matrix.SpecialLinearGroup (Fin 3) K}
    (hg : (g : Matrix (Fin 3) (Fin 3) K).IsUpperTriangular) (m : ℕ) (i : Fin 3) :
    ((g ^ m : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i i =
      (g : Matrix (Fin 3) (Fin 3) K) i i ^ m := by
  rw [Matrix.SpecialLinearGroup.coe_pow, l3r_pow_diag hg m i]

theorem l3r_sl_mul_diag {g h : Matrix.SpecialLinearGroup (Fin 3) K}
    (hg : (g : Matrix (Fin 3) (Fin 3) K).IsUpperTriangular)
    (hh : (h : Matrix (Fin 3) (Fin 3) K).IsUpperTriangular) (i : Fin 3) :
    ((g * h : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i i =
      (g : Matrix (Fin 3) (Fin 3) K) i i * (h : Matrix (Fin 3) (Fin 3) K) i i := by
  rw [Matrix.SpecialLinearGroup.coe_mul, mul_apply_self_of_isUpperTriangular hg hh i]

end Calculus

section Projective

variable {K : Type} [Field K]

theorem l3r_diag_of_proj_mem {M : Matrix.SpecialLinearGroup (Fin 3) K}
    (h : LinearFlag.proj 3 K M ∈ projUnitriangular 3 K) :
    (M : Matrix (Fin 3) (Fin 3) K) 0 0 = (M : Matrix (Fin 3) (Fin 3) K) 1 1 ∧
      (M : Matrix (Fin 3) (Fin 3) K) 1 1 = (M : Matrix (Fin 3) (Fin 3) K) 2 2 := by
  obtain ⟨u, hu, hpu⟩ := Subgroup.mem_map.mp h
  have hmem : u⁻¹ * M ∈ LinearFlag.scalars 3 K := QuotientGroup.eq.mp hpu
  obtain ⟨c, -, hcM⟩ := mem_scalars.mp hmem
  have hM' : (M : Matrix (Fin 3) (Fin 3) K) =
      (u : Matrix (Fin 3) (Fin 3) K) * scalar (Fin 3) (c : K) := by
    rw [← hcM, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
  have hdiag : ∀ i : Fin 3, (M : Matrix (Fin 3) (Fin 3) K) i i = (c : K) := by
    intro i
    have h1 : (u : Matrix (Fin 3) (Fin 3) K) i i = 1 := (mem_unitriangular.mp hu).2 i
    rw [hM', scalar_apply, Matrix.mul_diagonal, h1, one_mul]
  exact ⟨by rw [hdiag 0, hdiag 1], by rw [hdiag 1, hdiag 2]⟩

end Projective

section Odd

variable {K : Type} [Field K]

theorem l3r_odd_of_pow_eq_one {j : ℕ} {w : K} (h3 : w ^ 3 = 1) (hw : w ≠ 1)
    (hpow : w ^ (2 ^ j) * w = 1) : Odd j := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : w ^ (2 ^ j + 1) = 1 := by rw [pow_succ, hpow]
  have h2 : orderOf w = 3 := orderOf_eq_prime h3 hw
  have h4 : 3 ∣ 2 ^ j + 1 := by
    have := orderOf_dvd_of_pow_eq_one h1
    rwa [h2] at this
  exact l3_odd_of_three_dvd_two_pow_add_one h4

theorem l3r_odd_of_cube_pow {j : ℕ} {u v : K} (hu3 : u ^ 3 = v ^ 3) (huv : u ≠ v) (hv : v ≠ 0)
    (hpow : u ^ (2 ^ j) * u = v ^ (2 ^ j) * v) : Odd j := by
  have hv3 : v ^ 3 ≠ 0 := pow_ne_zero 3 hv
  have hE : v ^ (2 ^ j) * v ≠ 0 := mul_ne_zero (pow_ne_zero _ hv) hv
  refine l3r_odd_of_pow_eq_one (w := u * v⁻¹) ?_ ?_ ?_
  · rw [mul_pow, inv_pow, hu3, mul_inv_cancel₀ hv3]
  · intro h
    apply huv
    have hu : u = u * v⁻¹ * v := by rw [mul_assoc, inv_mul_cancel₀ hv, mul_one]
    rw [hu, h, one_mul]
  · calc (u * v⁻¹) ^ (2 ^ j) * (u * v⁻¹)
        = (u ^ (2 ^ j) * u) * (v ^ (2 ^ j) * v)⁻¹ := by
          rw [mul_pow, inv_pow, mul_inv]; ring
      _ = 1 := by rw [hpow, mul_inv_cancel₀ hE]

theorem l3r_fix_of_mul_inv {x y : K} (hy : y ≠ 0) (h : x * y⁻¹ = 1) : x = y :=
  (div_eq_one_iff_eq hy).mp (by rw [div_eq_mul_inv]; exact h)

theorem l3r_no_fix_of_odd {σ : K ≃+* K} {j n p : ℕ}
    (hj : ∀ x : K, σ x = x ^ 2 ^ j) (hn : Even n) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpn : p ∣ 2 ^ (n / 2) + 1) (hodd : Odd j) {a : Kˣ} (ha : orderOf a = p)
    (hfix : σ (a : K) = (a : K)) : False := by
  have hpow : (a : K) ^ 2 ^ j = (a : K) := by rw [← hj (a : K)]; exact hfix
  have hapow : a ^ 2 ^ j = a := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hpow)
  have hle : a ^ (2 ^ j - 1) * a = 1 * a := by
    rw [one_mul, ← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow, hapow]
  have h1 : a ^ (2 ^ j - 1) = 1 := mul_right_cancel hle
  have hdvd : p ∣ 2 ^ j - 1 := by
    rw [← ha]; exact orderOf_dvd_iff_pow_eq_one.mpr h1
  exact l3_not_dvd_two_pow_sub_one hn hp hp5 hpn hodd hdvd

theorem l3r_no_eta1 {σ : K ≃+* K} {p : ℕ} {a : Kˣ} (hp5 : 5 ≤ p) (ha : orderOf a = p)
    (h1 : ((a⁻¹ : Kˣ) : K) = σ (a : K) * (a : K))
    (h2 : σ (a : K) * (a : K) = σ ((a⁻¹ : Kˣ) : K)) : False := by
  have hσinv : σ ((a⁻¹ : Kˣ) : K) = (σ (a : K))⁻¹ := by
    rw [Units.val_inv_eq_inv_val]; exact map_inv₀ σ _
  have h3 : ((a⁻¹ : Kˣ) : K) = (σ (a : K))⁻¹ := by
    rw [← hσinv, ← h2]; exact h1
  have hfix : σ (a : K) = (a : K) := by
    rw [Units.val_inv_eq_inv_val, _root_.inv_inj] at h3
    exact h3.symm
  rw [hfix] at h1
  have h1' : (a : K)⁻¹ = (a : K) * (a : K) := by rw [← Units.val_inv_eq_inv_val]; exact h1
  have hne : (a : K) ≠ 0 := a.ne_zero
  have hcube : (a : K) ^ 3 = 1 := by
    calc (a : K) ^ 3 = ((a : K) * (a : K)) * (a : K) := by ring
      _ = (a : K)⁻¹ * (a : K) := by rw [h1']
      _ = 1 := inv_mul_cancel₀ hne
  have ha3 : a ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hcube, Units.val_one])
  have hdvd : p ∣ 3 := by rw [← ha]; exact orderOf_dvd_of_pow_eq_one ha3
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  omega

end Odd

section Witness

variable {K : Type} [Field K]

@[expose] def l3r_D (a : Kˣ) : Matrix.SpecialLinearGroup (Fin 3) K :=
  ⟨Matrix.diagonal ![(a : K), ((a⁻¹ : Kˣ) : K), 1], by
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    simp⟩

theorem l3r_D_coe (a : Kˣ) :
    ((l3r_D a : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal ![(a : K), ((a⁻¹ : Kˣ) : K), 1] := rfl

theorem l3r_D_inv (a : Kˣ) : (l3r_D a)⁻¹ = l3r_D a⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, l3r_D_coe,
    l3r_D_coe, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

theorem l3r_D_pow {a : Kˣ} {p : ℕ} (ha : orderOf a = p) : (l3r_D a) ^ p = 1 := by
  have hap : a ^ p = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have h0 : (a : K) ^ p = 1 := by rw [← Units.val_pow_eq_pow_val, hap, Units.val_one]
  have h1 : ((a⁻¹ : Kˣ) : K) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, inv_pow, hap, inv_one, Units.val_one]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, l3r_D_coe, Matrix.diagonal_pow,
    Matrix.SpecialLinearGroup.coe_one, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp [h0, h1]

theorem l3r_D_mem_upper (a : Kˣ) : l3r_D a ∈ upperTriangular 3 K := by
  rw [mem_upperTriangular_iff_isUpperTriangular, l3r_D_coe]
  exact l3r_diag_upper _

theorem l3r_mulD_00 (X : Matrix.SpecialLinearGroup (Fin 3) K) (a : Kˣ) :
    ((X * (l3r_D a)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) 0 0 =
      (X : Matrix (Fin 3) (Fin 3) K) 0 0 * ((a⁻¹ : Kˣ) : K) := by
  rw [l3r_D_inv, Matrix.SpecialLinearGroup.coe_mul, l3r_D_coe, Matrix.mul_diagonal]
  simp

theorem l3r_mulD_11 (X : Matrix.SpecialLinearGroup (Fin 3) K) (a : Kˣ) :
    ((X * (l3r_D a)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) 1 1 =
      (X : Matrix (Fin 3) (Fin 3) K) 1 1 * (a : K) := by
  rw [l3r_D_inv, Matrix.SpecialLinearGroup.coe_mul, l3r_D_coe, Matrix.mul_diagonal]
  simp

theorem l3r_mulD_22 (X : Matrix.SpecialLinearGroup (Fin 3) K) (a : Kˣ) :
    ((X * (l3r_D a)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) 2 2 =
      (X : Matrix (Fin 3) (Fin 3) K) 2 2 := by
  rw [l3r_D_inv, Matrix.SpecialLinearGroup.coe_mul, l3r_D_coe, Matrix.mul_diagonal]
  simp

end Witness

section Converse

variable {K : Type} [Field K]

theorem l3r_proj_mem_of_diag {M : Matrix.SpecialLinearGroup (Fin 3) K}
    (hM : (M : Matrix (Fin 3) (Fin 3) K).IsUpperTriangular)
    (h01 : (M : Matrix (Fin 3) (Fin 3) K) 0 0 = (M : Matrix (Fin 3) (Fin 3) K) 1 1)
    (h12 : (M : Matrix (Fin 3) (Fin 3) K) 1 1 = (M : Matrix (Fin 3) (Fin 3) K) 2 2) :
    LinearFlag.proj 3 K M ∈ projUnitriangular 3 K := by
  have hdet := l3r_det_diag hM
  rw [← h12, ← h01] at hdet
  have hs3 : (M : Matrix (Fin 3) (Fin 3) K) 0 0 ^ 3 = 1 := by linear_combination hdet
  have hs0 : (M : Matrix (Fin 3) (Fin 3) K) 0 0 ≠ 0 := by
    intro h0
    rw [h0] at hs3
    norm_num at hs3
  have hcu : (Units.mk0 _ hs0) ^ 3 = 1 :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hs3, Units.val_one])
  have hcinv : (Units.mk0 _ hs0)⁻¹ ^ 3 = 1 := by rw [inv_pow, hcu, inv_one]
  have hdiag : ∀ i : Fin 3,
      (M : Matrix (Fin 3) (Fin 3) K) i i = (M : Matrix (Fin 3) (Fin 3) K) 0 0 := by
    intro i
    fin_cases i
    · rfl
    · exact h01.symm
    · exact h12.symm.trans h01.symm
  refine Subgroup.mem_map.mpr ⟨scalarElement _ hcinv * M, ?_, ?_⟩
  · refine mem_unitriangular.mpr ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [Matrix.SpecialLinearGroup.coe_mul, coe_scalarElement, scalar_apply,
        Matrix.diagonal_mul, hM hij, mul_zero]
    · rw [Matrix.SpecialLinearGroup.coe_mul, coe_scalarElement, scalar_apply,
        Matrix.diagonal_mul, hdiag i]
      simp [hs0]
  · rw [map_mul, (proj_eq_one_iff).mpr (scalarElement_mem_scalars _ hcinv), one_mul]

end Converse

section Lift

variable {K : Type} [Field K]

@[expose] noncomputable def l3r_lift (A : GL (Fin 3) K) (σ : K ≃+* K) (η : ℕ) :
    MulAut (Matrix.SpecialLinearGroup (Fin 3) K) :=
  CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K A *
    CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 3) K σ *
    (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K
        (CFSG.ASVolI.burnsideF411a_w0 K) *
      CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 3 K) ^ η

theorem l3r_fieldAut_refl : LinearFlag.fieldAut 3 K (RingEquiv.refl K) = 1 := by
  rw [show RingEquiv.refl K = (1 : K ≃+* K) from rfl, map_one]

theorem l3r_descend (A : GL (Fin 3) K) (σ : K ≃+* K) (η : ℕ) :
    LinearFlag.descendAut 3 K (l3r_lift A σ η) =
      LinearFlag.conjAut 3 K A * LinearFlag.fieldAut 3 K σ *
        CFSG.ASVolI.burnsideF411a_L3zeta K (RingEquiv.refl K) ^ η := by
  rw [CFSG.ASVolI.burnsideF411a_L3zeta, l3r_fieldAut_refl, mul_one]
  simp only [l3r_lift, map_mul, map_pow]
  rfl

theorem l3r_lift_zero_apply (A : GL (Fin 3) K) (σ : K ≃+* K)
    (g : Matrix.SpecialLinearGroup (Fin 3) K) :
    l3r_lift A σ 0 g =
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K A
        (CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 3) K σ g) := by
  rw [l3r_lift, pow_zero, mul_one]
  rfl

theorem l3r_lift_one_apply (A : GL (Fin 3) K) (σ : K ≃+* K)
    (g : Matrix.SpecialLinearGroup (Fin 3) K) :
    l3r_lift A σ 1 g =
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K A
        (CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 3) K σ
          (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K
            (CFSG.ASVolI.burnsideF411a_w0 K)
            (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 3 K g))) := by
  rw [l3r_lift, pow_one]
  rfl

theorem l3r_field_entry (σ : K ≃+* K) (g : Matrix.SpecialLinearGroup (Fin 3) K) (i j : Fin 3) :
    ((CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 3) K σ g :
        Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j =
      σ ((g : Matrix (Fin 3) (Fin 3) K) i j) := rfl

theorem l3r_field_upper (σ : K ≃+* K) {g : Matrix.SpecialLinearGroup (Fin 3) K}
    (hg : (g : Matrix (Fin 3) (Fin 3) K).IsUpperTriangular) :
    ((CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 3) K σ g :
        Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsUpperTriangular := by
  intro i j hij
  rw [l3r_field_entry, hg hij, map_zero]

theorem l3r_lift0_upper (A : GL (Fin 3) K) (hA : (A : Matrix (Fin 3) (Fin 3) K).IsUpperTriangular)
    (σ : K ≃+* K) {g : Matrix.SpecialLinearGroup (Fin 3) K}
    (hg : (g : Matrix (Fin 3) (Fin 3) K).IsUpperTriangular) :
    ((l3r_lift A σ 0 g : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).IsUpperTriangular := by
  rw [l3r_lift_zero_apply, LinearFlag.coe_slConjugation]
  exact Matrix.BlockTriangular.mul (Matrix.BlockTriangular.mul hA (l3r_field_upper σ hg))
    (l3r_inv_isUpper A hA)

theorem l3r_lift0_diag (A : GL (Fin 3) K) (hA : (A : Matrix (Fin 3) (Fin 3) K).IsUpperTriangular)
    (σ : K ≃+* K) {g : Matrix.SpecialLinearGroup (Fin 3) K}
    (hg : (g : Matrix (Fin 3) (Fin 3) K).IsUpperTriangular) (i : Fin 3) :
    ((l3r_lift A σ 0 g : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) i i = σ ((g : Matrix (Fin 3) (Fin 3) K) i i) := by
  rw [l3r_lift_zero_apply, LinearFlag.coe_slConjugation,
    l3r_conj_diag A hA _ (l3r_field_upper σ hg) i]
  exact l3r_field_entry σ g i i

theorem l3r_w0_val :
    ((CFSG.ASVolI.burnsideF411a_w0 K : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl

theorem l3r_E_coe (a : Kˣ) :
    ((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K
        (CFSG.ASVolI.burnsideF411a_w0 K)
        (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 3 K (l3r_D a)) :
      Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal ![1, (a : K), ((a⁻¹ : Kˣ) : K)] := by
  rw [LinearFlag.coe_slConjugation,
    CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut_matrix, l3r_D_inv, l3r_D_coe,
    CFSG.ASVolI.burnsideF411a_w0_inv, l3r_w0_val, Matrix.diagonal_transpose]
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply, Matrix.of_apply,
    Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  fin_cases i <;> fin_cases j <;> simp

theorem l3r_F_coe (σ : K ≃+* K) (a : Kˣ) :
    ((CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 3) K σ
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K
          (CFSG.ASVolI.burnsideF411a_w0 K)
          (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 3 K (l3r_D a))) :
      Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal ![1, σ (a : K), σ ((a⁻¹ : Kˣ) : K)] := by
  ext i j
  rw [l3r_field_entry, l3r_E_coe]
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

theorem l3r_F_upper (σ : K ≃+* K) (a : Kˣ) :
    ((CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 3) K σ
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K
          (CFSG.ASVolI.burnsideF411a_w0 K)
          (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 3 K (l3r_D a))) :
      Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsUpperTriangular := by
  rw [l3r_F_coe]
  exact l3r_diag_upper _

theorem l3r_lift1_diag (A : GL (Fin 3) K) (hA : (A : Matrix (Fin 3) (Fin 3) K).IsUpperTriangular)
    (σ : K ≃+* K) (a : Kˣ) (i : Fin 3) :
    ((l3r_lift A σ 1 (l3r_D a) : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) i i =
      Matrix.diagonal ![(1 : K), σ (a : K), σ ((a⁻¹ : Kˣ) : K)] i i := by
  rw [l3r_lift_one_apply, LinearFlag.coe_slConjugation,
    l3r_conj_diag A hA _ (l3r_F_upper σ a) i, l3r_F_coe]

end Lift

section Images

variable {K : Type} [Field K]

theorem l3r_eta0_diag (A : GL (Fin 3) K) (hA : (A : Matrix (Fin 3) (Fin 3) K).IsUpperTriangular)
    (σ : K ≃+* K) (a : Kˣ) :
    ((l3r_lift A σ 0 (l3r_D a) * (l3r_D a)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) 0 0 = σ (a : K) * ((a⁻¹ : Kˣ) : K) ∧
      ((l3r_lift A σ 0 (l3r_D a) * (l3r_D a)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) 1 1 = σ ((a⁻¹ : Kˣ) : K) * (a : K) ∧
      ((l3r_lift A σ 0 (l3r_D a) * (l3r_D a)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
  have hD : ((l3r_D a : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).IsUpperTriangular := by
    rw [l3r_D_coe]
    exact l3r_diag_upper _
  refine ⟨?_, ?_, ?_⟩
  · rw [l3r_mulD_00, l3r_lift0_diag A hA σ hD 0]
    simp [l3r_D_coe]
  · rw [l3r_mulD_11, l3r_lift0_diag A hA σ hD 1]
    simp [l3r_D_coe]
  · rw [l3r_mulD_22, l3r_lift0_diag A hA σ hD 2]
    simp [l3r_D_coe]

theorem l3r_eta1_diag (A : GL (Fin 3) K) (hA : (A : Matrix (Fin 3) (Fin 3) K).IsUpperTriangular)
    (σ : K ≃+* K) (a : Kˣ) :
    ((l3r_lift A σ 1 (l3r_D a) * (l3r_D a)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) 0 0 = ((a⁻¹ : Kˣ) : K) ∧
      ((l3r_lift A σ 1 (l3r_D a) * (l3r_D a)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) 1 1 = σ (a : K) * (a : K) ∧
      ((l3r_lift A σ 1 (l3r_D a) * (l3r_D a)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) 2 2 = σ ((a⁻¹ : Kˣ) : K) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [l3r_mulD_00, l3r_lift1_diag A hA σ a 0]
    simp
  · rw [l3r_mulD_11, l3r_lift1_diag A hA σ a 1]
    simp
  · rw [l3r_mulD_22, l3r_lift1_diag A hA σ a 2]
    simp

end Images

theorem l3_rclaim_P {K : Type} [Field K] [Finite K] [CharP K 2]
    (hCP : ∀ β : MulAut (projectiveSL 3 K), (projUnitriangular 3 K).map β.toMonoidHom =
      projUnitriangular 3 K → ∃ (A : GL (Fin 3) K) (σ : K ≃+* K) (η : ℕ), η ≤ 1 ∧
        (∀ i j : Fin 3, j < i → (A : Matrix (Fin 3) (Fin 3) K) i j = 0) ∧
        β = CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut 3 K A *
          CFSG.LocalAnalysis.ComponentInitial.LinearFlag.fieldAut 3 K σ *
          CFSG.ASVolI.burnsideF411a_L3zeta K (RingEquiv.refl K) ^ η)
    {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : Even n) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpn : p ∣ 2 ^ (n / 2) + 1) (α : MulAut (projectiveSL 3 K))
    (hα : (projUnitriangular 3 K).map α.toMonoidHom = projUnitriangular 3 K)
    {c : projectiveSL 3 K} (hc : c ∈ projUpperTriangular 3 K) (hcU : c ∉ projUnitriangular 3 K)
    (hc3 : c ^ 3 ∈ projUnitriangular 3 K) (hcr : α c * c ∈ projUnitriangular 3 K) :
    ∃ b ∈ projUpperTriangular 3 K, b ^ p ∈ projUnitriangular 3 K ∧
      α b * b⁻¹ ∉ projUnitriangular 3 K := by
  obtain ⟨A, σ, η, hη, hAup, hαeq⟩ := hCP α hα
  have hA : (A : Matrix (Fin 3) (Fin 3) K).IsUpperTriangular := fun i j h => hAup i j h
  have hαproj : ∀ g : Matrix.SpecialLinearGroup (Fin 3) K,
      α (LinearFlag.proj 3 K g) = LinearFlag.proj 3 K (l3r_lift A σ η g) := by
    intro g
    rw [← LinearFlag.descendAut_proj 3 K (l3r_lift A σ η) g, l3r_descend, ← hαeq]
  obtain ⟨j, hj⟩ := l2_ringEquiv_pow σ
  obtain ⟨a, ha⟩ := l3_exists_orderOf_eq_prime hK hn hp hpn
  have hαD : α (LinearFlag.proj 3 K (l3r_D a)) * (LinearFlag.proj 3 K (l3r_D a))⁻¹ =
      LinearFlag.proj 3 K (l3r_lift A σ η (l3r_D a) * (l3r_D a)⁻¹) := by
    rw [hαproj, ← map_inv, ← map_mul]
  obtain rfl | rfl : η = 0 ∨ η = 1 := by omega
  ·
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hc
    have hgU : (g : Matrix (Fin 3) (Fin 3) K).IsUpperTriangular := fun i j h => hg i j h
    have hdet := l3r_det_diag hgU
    have hg11 : (g : Matrix (Fin 3) (Fin 3) K) 1 1 ≠ 0 := by
      intro h
      rw [h] at hdet
      simp at hdet
    have hg22 : (g : Matrix (Fin 3) (Fin 3) K) 2 2 ≠ 0 := by
      intro h
      rw [h] at hdet
      simp at hdet
    have hne : ¬ ((g : Matrix (Fin 3) (Fin 3) K) 0 0 = (g : Matrix (Fin 3) (Fin 3) K) 1 1 ∧
        (g : Matrix (Fin 3) (Fin 3) K) 1 1 = (g : Matrix (Fin 3) (Fin 3) K) 2 2) :=
      fun h => hcU (l3r_proj_mem_of_diag hgU h.1 h.2)
    have hc3' := hc3
    rw [← map_pow] at hc3'
    obtain ⟨h3a, h3b⟩ := l3r_diag_of_proj_mem hc3'
    have hcr' := hcr
    rw [hαproj, ← map_mul] at hcr'
    obtain ⟨h4a, h4b⟩ := l3r_diag_of_proj_mem hcr'
    have hLg := l3r_lift0_upper A hA σ hgU
    simp only [l3r_sl_pow_diag hgU, l3r_sl_mul_diag hLg hgU, l3r_lift0_diag A hA σ hgU, hj]
      at h3a h3b h4a h4b
    have hodd : Odd j := by
      rcases not_and_or.mp hne with hxy | hyz
      · exact l3r_odd_of_cube_pow h3a hxy hg11 h4a
      · exact l3r_odd_of_cube_pow h3b hyz hg22 h4b
    refine ⟨LinearFlag.proj 3 K (l3r_D a), Subgroup.mem_map_of_mem _ (l3r_D_mem_upper a), ?_, ?_⟩
    · rw [← map_pow, l3r_D_pow ha, map_one]
      exact one_mem _
    · intro hmem
      rw [hαD] at hmem
      obtain ⟨h1, h2⟩ := l3r_diag_of_proj_mem hmem
      obtain ⟨e0, e1, e2⟩ := l3r_eta0_diag A hA σ a
      have h00 : σ (a : K) * (a : K)⁻¹ = 1 := by
        rw [← Units.val_inv_eq_inv_val, ← e0, h1, h2, e2]
      exact l3r_no_fix_of_odd hj hn hp hp5 hpn hodd ha (l3r_fix_of_mul_inv (Units.ne_zero a) h00)
  ·
    refine ⟨LinearFlag.proj 3 K (l3r_D a), Subgroup.mem_map_of_mem _ (l3r_D_mem_upper a), ?_, ?_⟩
    · rw [← map_pow, l3r_D_pow ha, map_one]
      exact one_mem _
    · intro hmem
      rw [hαD] at hmem
      obtain ⟨h1, h2⟩ := l3r_diag_of_proj_mem hmem
      obtain ⟨e0, e1, e2⟩ := l3r_eta1_diag A hA σ a
      exact l3r_no_eta1 hp5 ha (e0.symm.trans (h1.trans e1)) (e1.symm.trans (h2.trans e2))

theorem l3_rclaim_S {K : Type} [Field K] [Finite K] [CharP K 2]
    (hCP : ∀ β : MulAut (projectiveSL 3 K), (projUnitriangular 3 K).map β.toMonoidHom =
      projUnitriangular 3 K → ∃ (A : GL (Fin 3) K) (σ : K ≃+* K) (η : ℕ), η ≤ 1 ∧
        (∀ i j : Fin 3, j < i → (A : Matrix (Fin 3) (Fin 3) K) i j = 0) ∧
        β = CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut 3 K A *
          CFSG.LocalAnalysis.ComponentInitial.LinearFlag.fieldAut 3 K σ *
          CFSG.ASVolI.burnsideF411a_L3zeta K (RingEquiv.refl K) ^ η)
    {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : Even n) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpn : p ∣ 2 ^ (n / 2) + 1) (α : MulAut (Matrix.SpecialLinearGroup (Fin 3) K))
    (hα : (unitriangular 3 K).map α.toMonoidHom = unitriangular 3 K)
    {c : Matrix.SpecialLinearGroup (Fin 3) K} (hc : c ∈ upperTriangular 3 K)
    (hcU : c ∉ unitriangular 3 K) (hc3 : c ^ 3 ∈ unitriangular 3 K)
    (hcr : α c * c ∈ unitriangular 3 K) :
    ∃ b ∈ upperTriangular 3 K, b ^ p ∈ unitriangular 3 K ∧ α b * b⁻¹ ∉ unitriangular 3 K := by
  have hbarU : (projUnitriangular 3 K).map (LinearFlag.descendAut 3 K α).toMonoidHom =
      projUnitriangular 3 K := by
    rw [projUnitriangular, Subgroup.map_map]
    have hcomp : ((LinearFlag.descendAut 3 K α).toMonoidHom.comp (LinearFlag.proj 3 K)) =
        (LinearFlag.proj 3 K).comp α.toMonoidHom := by
      ext g
      exact LinearFlag.descendAut_proj 3 K α g
    rw [hcomp, ← Subgroup.map_map, hα]
  obtain ⟨A, σ, η, hη, hAup, hbar⟩ := hCP _ hbarU
  have hA : (A : Matrix (Fin 3) (Fin 3) K).IsUpperTriangular := fun i j h => hAup i j h
  have hbar' : LinearFlag.descendAut 3 K α = LinearFlag.descendAut 3 K (l3r_lift A σ η) := by
    rw [l3r_descend, hbar]
  have hαproj : ∀ g : Matrix.SpecialLinearGroup (Fin 3) K,
      LinearFlag.proj 3 K (α g) = LinearFlag.proj 3 K (l3r_lift A σ η g) := by
    intro g
    rw [← LinearFlag.descendAut_proj 3 K α g,
      ← LinearFlag.descendAut_proj 3 K (l3r_lift A σ η) g, hbar']
  haveI : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) K) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (K := K) (n := 3) le_rfl
  have hEq : α.toMonoidHom = (l3r_lift A σ η).toMonoidHom := by
    apply bt_eq_of_inv_mul_mem_center
    intro g
    rw [← LinearFlag.scalars_eq_center 3 K]
    exact QuotientGroup.eq.mp (hαproj g)
  have hαL : ∀ g, α g = l3r_lift A σ η g := fun g => by
    have h := congrArg
      (fun f : Matrix.SpecialLinearGroup (Fin 3) K →* Matrix.SpecialLinearGroup (Fin 3) K => f g)
      hEq
    exact h
  obtain ⟨j, hj⟩ := l2_ringEquiv_pow σ
  obtain ⟨a, ha⟩ := l3_exists_orderOf_eq_prime hK hn hp hpn
  obtain rfl | rfl : η = 0 ∨ η = 1 := by omega
  ·
    have hcup : ∀ i j : Fin 3, j < i → (c : Matrix (Fin 3) (Fin 3) K) i j = 0 :=
      mem_upperTriangular.mp hc
    have hcU_up : (c : Matrix (Fin 3) (Fin 3) K).IsUpperTriangular := fun i j h => hcup i j h
    have hcU' : ¬ ((c : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 ∧
        (c : Matrix (Fin 3) (Fin 3) K) 1 1 = 1 ∧ (c : Matrix (Fin 3) (Fin 3) K) 2 2 = 1) := by
      rintro ⟨e0, e1, e2⟩
      apply hcU
      refine mem_unitriangular.mpr ⟨hcup, fun i => ?_⟩
      fin_cases i <;> simp [e0, e1, e2]
    have hx3 : ∀ i : Fin 3, (c : Matrix (Fin 3) (Fin 3) K) i i ^ 3 = 1 := fun i => by
      rw [← l3r_sl_pow_diag hcU_up 3 i]
      exact (mem_unitriangular.mp hc3).2 i
    have hσc : ∀ i : Fin 3,
        σ ((c : Matrix (Fin 3) (Fin 3) K) i i) * (c : Matrix (Fin 3) (Fin 3) K) i i = 1 := fun i => by
      have h := (mem_unitriangular.mp hcr).2 i
      rw [hαL c, l3r_sl_mul_diag (l3r_lift0_upper A hA σ hcU_up) hcU_up i,
        l3r_lift0_diag A hA σ hcU_up i] at h
      exact h
    have key : ∀ w : K, w ^ 3 = 1 → σ w * w = 1 → w ≠ 1 → Odd j := fun w h3 hw1 hw =>
      l3r_odd_of_pow_eq_one h3 hw (by rw [← hj w]; exact hw1)
    have hodd : Odd j := by
      by_cases e0 : (c : Matrix (Fin 3) (Fin 3) K) 0 0 = 1
      · by_cases e1 : (c : Matrix (Fin 3) (Fin 3) K) 1 1 = 1
        · exact key _ (hx3 2) (hσc 2) (fun e2 => hcU' ⟨e0, e1, e2⟩)
        · exact key _ (hx3 1) (hσc 1) e1
      · exact key _ (hx3 0) (hσc 0) e0
    refine ⟨l3r_D a, l3r_D_mem_upper a, ?_, ?_⟩
    · rw [l3r_D_pow ha]
      exact one_mem _
    · intro hmem
      rw [hαL] at hmem
      obtain ⟨e0, -, -⟩ := l3r_eta0_diag A hA σ a
      have h1 := (mem_unitriangular.mp hmem).2 0
      rw [e0] at h1
      have h1' : σ (a : K) * (a : K)⁻¹ = 1 := by
        rw [← Units.val_inv_eq_inv_val]
        exact h1
      exact l3r_no_fix_of_odd hj hn hp hp5 hpn hodd ha (l3r_fix_of_mul_inv (Units.ne_zero a) h1')
  ·
    refine ⟨l3r_D a, l3r_D_mem_upper a, ?_, ?_⟩
    · rw [l3r_D_pow ha]
      exact one_mem _
    · intro hmem
      rw [hαL] at hmem
      obtain ⟨e0, -, -⟩ := l3r_eta1_diag A hA σ a
      have h1 := (mem_unitriangular.mp hmem).2 0
      rw [e0] at h1
      have ha1 : a = 1 := inv_eq_one.mp (Units.ext h1)
      rw [ha1, orderOf_one] at ha
      omega

end CFSG.Quasithin.H13.P31X
