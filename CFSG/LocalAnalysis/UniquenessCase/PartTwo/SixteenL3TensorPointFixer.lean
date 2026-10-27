module

public import CFSG.Quasithin.Background.HL3WrBlock

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin.H CFSG.Quasithin.H.L3Wr CFSG.Quasithin.H13
open scoped Matrix

private def tensorFixC2 : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![0, 1; 1, 1]

private abbrev tensorFixD0 (r n : ℕ) : Matrix (Fin r ⊕ Fin n) (Fin r ⊕ Fin n) (ZMod 2) :=
  Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) (ZMod 2)) 0 0
    (0 : Matrix (Fin n) (Fin n) (ZMod 2))

private theorem tensorFix_exists_block (r n : ℕ) (hn : n = 3 - r)
    (hr : r = 1 ∨ r = 2 ∨ r = 3) :
    ∃ a0 b0 : Matrix (Fin r ⊕ Fin n) (Fin r ⊕ Fin n) (ZMod 2),
      a0 * tensorFixD0 r n * b0ᵀ = tensorFixD0 r n ∧ a0 ^ 3 = 1 ∧ a0 ≠ 1 ∧ b0 ^ 3 = 1 := by
  rcases hr with rfl | rfl | rfl
  · subst hn
    let a0 : Matrix (Fin 1 ⊕ Fin 2) (Fin 1 ⊕ Fin 2) (ZMod 2) :=
      Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) (ZMod 2)) 0 0 tensorFixC2
    let b0 : Matrix (Fin 1 ⊕ Fin 2) (Fin 1 ⊕ Fin 2) (ZMod 2) := a0
    have hne : a0 ≠ 1 := by decide +kernel
    refine ⟨a0, a0, ?_, ?_, hne, ?_⟩
    all_goals
      ext i j
      rcases i with i | i <;> rcases j with j | j <;>
        fin_cases i <;> fin_cases j <;>
        simp [a0, tensorFixC2, Matrix.mul_apply, Fin.sum_univ_two, pow_succ] <;> decide
  · subst hn
    let a0 : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) (ZMod 2) :=
      Matrix.fromBlocks tensorFixC2 0 0 (1 : Matrix (Fin 1) (Fin 1) (ZMod 2))
    let b0 : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) (ZMod 2) :=
      Matrix.fromBlocks (tensorFixC2 * tensorFixC2) 0 0
        (1 : Matrix (Fin 1) (Fin 1) (ZMod 2))
    have hne : a0 ≠ 1 := by decide +kernel
    refine ⟨a0, b0, ?_, ?_, hne, ?_⟩
    all_goals
      ext i j
      rcases i with i | i <;> rcases j with j | j <;>
        fin_cases i <;> fin_cases j <;>
        simp [a0, b0, tensorFixC2, Matrix.mul_apply, Fin.sum_univ_two, pow_succ] <;> decide
  · subst hn
    let a0 : Matrix (Fin 3 ⊕ Fin 0) (Fin 3 ⊕ Fin 0) (ZMod 2) :=
      Matrix.fromBlocks cBm 0 0 (1 : Matrix (Fin 0) (Fin 0) (ZMod 2))
    let b0 : Matrix (Fin 3 ⊕ Fin 0) (Fin 3 ⊕ Fin 0) (ZMod 2) :=
      Matrix.fromBlocks (cBm * cBm) 0 0 (1 : Matrix (Fin 0) (Fin 0) (ZMod 2))
    have hne : a0 ≠ 1 := by decide +kernel
    refine ⟨a0, b0, ?_, ?_, hne, ?_⟩
    all_goals
      ext i j
      rcases i with i | i <;> rcases j with j | j <;>
        fin_cases i <;> fin_cases j <;>
        simp [a0, b0, cBm, Matrix.mul_apply, Fin.sum_univ_three, pow_succ] <;> decide

private theorem tensorFix_exists_img (X : Matrix (Fin 3) (Fin 3) (ZMod 2)) (hX : X ≠ 0) :
    ∃ c ∈ img, orderOf c = 3 ∧ c (Multiplicative.ofAdd X) = Multiplicative.ofAdd X := by
  classical
  obtain ⟨V, U, e, hVunit, hUunit, hVXU⟩ := Matrix.exists_rank_normal_form X
  let n := Fintype.card (Fin 3) - X.rank
  let D : Matrix (Fin 3) (Fin 3) (ZMod 2) := (tensorFixD0 X.rank n).submatrix e e
  have hVXU' : V * X * U = D := by
    simpa only [D, tensorFixD0, n] using hVXU
  have hD0_zero : tensorFixD0 0 n = 0 := by
    ext i j
    rcases i with i | i
    · exact Fin.elim0 i
    rcases j with j | j
    · exact Fin.elim0 j
    · simp only [tensorFixD0, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]
  have hr0 : X.rank ≠ 0 := by
    intro hr
    have hD0' : tensorFixD0 X.rank n = 0 := by
      rw [hr]
      exact hD0_zero
    have hDzero : D = 0 := by
      change (tensorFixD0 X.rank n).submatrix e e = 0
      rw [hD0', Matrix.submatrix_zero]
      simp
    have hVXzero : V * X * U = 0 := hVXU'.trans hDzero
    have hVX : V * X = 0 := (IsUnit.mul_left_eq_zero hUunit).mp hVXzero
    exact hX ((IsUnit.mul_right_eq_zero hVunit).mp hVX)
  have hrle : X.rank ≤ 3 := Matrix.rank_le_width X
  have hr : X.rank = 1 ∨ X.rank = 2 ∨ X.rank = 3 := by omega
  have hn : n = 3 - X.rank := by
    simp only [n, Fintype.card_fin]
  obtain ⟨a0, b0, hfix0, ha0pow, ha0ne, hb0pow⟩ := tensorFix_exists_block X.rank n hn hr
  let R : Matrix (Fin X.rank ⊕ Fin n) (Fin X.rank ⊕ Fin n) (ZMod 2) ≃+*
      Matrix (Fin 3) (Fin 3) (ZMod 2) :=
    Matrix.reindexRingEquiv (ZMod 2) e.symm
  let aM : Matrix (Fin 3) (Fin 3) (ZMod 2) := R a0
  let bM : Matrix (Fin 3) (Fin 3) (ZMod 2) := R b0
  have hDM : D = R (tensorFixD0 X.rank n) := rfl
  have hbMt : bMᵀ = R (b0ᵀ) := by
    change (R b0)ᵀ = R (b0ᵀ)
    exact Matrix.transpose_reindex e.symm e.symm b0
  have haMpow : aM ^ 3 = 1 := by
    change (R a0) ^ 3 = 1
    rw [← map_pow, ha0pow, map_one]
  have hbMpow : bM ^ 3 = 1 := by
    change (R b0) ^ 3 = 1
    rw [← map_pow, hb0pow, map_one]
  have haMne : aM ≠ 1 := by
    intro h
    apply ha0ne
    apply R.injective
    simpa only [aM, map_one] using h
  have hfixM : aM * D * bMᵀ = D := by
    rw [hDM, hbMt]
    change R a0 * R (tensorFixD0 X.rank n) * R (b0ᵀ) = R (tensorFixD0 X.rank n)
    rw [← map_mul, ← map_mul, hfix0]
  have hdeta : aM.det ≠ 0 := by
    have hunit : IsUnit aM := IsUnit.of_pow_eq_one haMpow (by norm_num)
    exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det aM).mp hunit)
  have hdetb : bM.det ≠ 0 := by
    have hunit : IsUnit bM := IsUnit.of_pow_eq_one hbMpow (by norm_num)
    exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det bM).mp hunit)
  let a : ↥SL32 := slOfMat aM hdeta
  let b : ↥SL32 := slOfMat bM hdetb
  have hmata : mat a = aM := mat_slOfMat aM hdeta
  have hmatb : mat b = bM := mat_slOfMat bM hdetb
  have ha3 : a ^ 3 = 1 := by
    apply eq_of_mat_eq
    simp only [mat_pow, hmata, haMpow, mat_one]
  have hb3 : b ^ 3 = 1 := by
    apply eq_of_mat_eq
    simp only [mat_pow, hmatb, hbMpow, mat_one]
  have hane : a ≠ 1 := by
    intro h
    apply haMne
    rw [← hmata, h, mat_one]
  let v : ↥SL32 := ⟨hVunit.unit, mem_SL32 _⟩
  let u : ↥SL32 := ⟨hUunit.unit, mem_SL32 _⟩
  have hmv : mat v = V := hVunit.unit_spec
  have hmu : mat u = U := hUunit.unit_spec
  have hVXU'' : mat v * X * mat u = D := by
    rw [hmv, hmu]
    exact hVXU'
  have hmain : mat a * D * (mat b)ᵀ = D := by
    rw [hmata, hmatb]
    exact hfixM
  have hd_inv : mat ((dualSL u)⁻¹) = (mat u)ᵀ := by
    have h1 : mat ((dualSL u)⁻¹) * mat (dualSL u) = 1 := mat_inv_mul (dualSL u)
    have h2 : (mat u)ᵀ * mat (dualSL u) = 1 := by
      rw [mat_dualSL, ← Matrix.transpose_mul, mat_inv_mul u, Matrix.transpose_one]
    exact IsUnit.mul_right_cancel ((dualSL u : GL (Fin 3) (ZMod 2)).isUnit) (h1.trans h2.symm)
  have hbXt : (mat (dualSL u * b * (dualSL u)⁻¹))ᵀ =
      mat u * (mat b)ᵀ * mat u⁻¹ := by
    calc
      (mat (dualSL u * b * (dualSL u)⁻¹))ᵀ
          = (mat ((dualSL u)⁻¹))ᵀ * (mat b)ᵀ * (mat (dualSL u))ᵀ := by
            rw [mat_mul, mat_mul, Matrix.transpose_mul, Matrix.transpose_mul]
            simp only [Matrix.mul_assoc]
      _ = mat u * (mat b)ᵀ * mat u⁻¹ := by
            rw [hd_inv, mat_dualSL]
            simp only [Matrix.transpose_transpose, Matrix.mul_assoc]
  let aX : ↥SL32 := v⁻¹ * a * v
  let bX : ↥SL32 := dualSL u * b * (dualSL u)⁻¹
  have hmat_aX : mat aX = mat v⁻¹ * mat a * mat v := by
    simp only [aX, mat_mul]
  have hfixX : mat aX * X * (mat bX)ᵀ = X := by
    rw [hmat_aX, hbXt]
    rw [← Matrix.mul_assoc (((mat v⁻¹ * mat a) * mat v) * X) (mat u * (mat b)ᵀ) (mat u⁻¹)]
    rw [← Matrix.mul_assoc (((mat v⁻¹ * mat a) * mat v) * X) (mat u) (mat b)ᵀ]
    rw [Matrix.mul_assoc ((mat v⁻¹ * mat a) * mat v) X (mat u)]
    rw [Matrix.mul_assoc (mat v⁻¹ * mat a) (mat v) (X * mat u)]
    rw [← Matrix.mul_assoc (mat v) X (mat u)]
    rw [hVXU'']
    rw [Matrix.mul_assoc (mat v⁻¹) (mat a) D]
    rw [Matrix.mul_assoc (mat v⁻¹) (mat a * D) (mat b)ᵀ]
    rw [hmain]
    rw [← hVXU'']
    rw [Matrix.mul_assoc (mat v) X (mat u)]
    rw [← Matrix.mul_assoc (mat v⁻¹) (mat v) (X * mat u)]
    rw [mat_inv_mul v, Matrix.one_mul]
    rw [Matrix.mul_assoc X (mat u) (mat u⁻¹), mat_mul_inv u, Matrix.mul_one]
  have haX3 : aX ^ 3 = 1 := by
    show (v⁻¹ * a * v) ^ 3 = 1
    rw [show v⁻¹ * a * v = MulAut.conj v⁻¹ a by
      rw [MulAut.conj_apply, inv_inv]]
    rw [← map_pow, ha3, map_one]
  have hbX3 : bX ^ 3 = 1 := by
    show (dualSL u * b * (dualSL u)⁻¹) ^ 3 = 1
    rw [show dualSL u * b * (dualSL u)⁻¹ = MulAut.conj (dualSL u) b by
      rw [MulAut.conj_apply]]
    rw [← map_pow, hb3, map_one]
  have haXne : aX ≠ 1 := by
    intro h
    apply hane
    have hconj : a = v * aX * v⁻¹ := by
      show a = v * (v⁻¹ * a * v) * v⁻¹
      group
    rw [h] at hconj
    simpa using hconj
  have hpair3 : (aX, bX) ^ 3 = 1 := by
    change (aX ^ 3, bX ^ 3) = 1
    rw [haX3, hbX3]
    rfl
  have hpairne : (aX, bX) ≠ 1 := by
    intro h
    exact haXne (congrArg Prod.fst h)
  have hpairord : orderOf (aX, bX) = 3 := orderOf_eq_prime hpair3 hpairne
  refine ⟨rho (aX, bX), rho_mem_img (aX, bX), ?_, ?_⟩
  · rw [orderOf_injective rho rho_injective (aX, bX)]
    exact hpairord
  · apply Multiplicative.toAdd.injective
    simpa only [toAdd_rho, toAdd_ofAdd] using hfixX

theorem tensorPair_exists_order_three_fix {W : Type*} [CommGroup W]
    {H : Subgroup (MulAut W)}
    (hreal : (tensorPairModel SL32 SL32).RealizesMod H) :
    ∀ x : W, x ≠ 1 → ∃ b ∈ H, orderOf b = 3 ∧ b x = x := by
  intro x hx
  obtain ⟨e, he⟩ := exists_model hreal
  have hex : e x ≠ 1 := by
    intro h
    exact hx (e.injective (by simpa using h))
  have hXne : Multiplicative.toAdd (e x) ≠ 0 := by
    intro h
    exact hex (Multiplicative.toAdd.injective (by simpa using h))
  obtain ⟨c, hcimg, hc3, hcfix⟩ := tensorFix_exists_img (Multiplicative.toAdd (e x)) hXne
  have he' : H.map (MulAut.congr e).toMonoidHom = img := he
  have hcH : c ∈ H.map (MulAut.congr e).toMonoidHom := by
    rw [he']
    exact hcimg
  obtain ⟨b, hbH, hbc⟩ := Subgroup.mem_map.mp hcH
  refine ⟨b, hbH, ?_, ?_⟩
  · have hordc : orderOf c = orderOf b := by
      rw [← hbc]
      exact MulEquiv.orderOf_eq (MulAut.congr e) b
    rw [← hordc]
    exact hc3
  · apply e.injective
    calc
      e (b x) = ((MulAut.congr e) b) (e x) := by
        rw [show (MulAut.congr e) b = e.symm.trans (b.trans e) from rfl]
        rw [MulEquiv.trans_apply, MulEquiv.trans_apply, e.symm_apply_apply]
      _ = c (e x) := by
        change ((MulAut.congr e).toMonoidHom b) (e x) = c (e x)
        rw [hbc]
      _ = e x := hcfix

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
