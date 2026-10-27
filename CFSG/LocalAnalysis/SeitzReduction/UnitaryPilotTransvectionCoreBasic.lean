module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherIsotropicRadical

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Matrix CFSG.LocalAnalysis.ComponentInitial

section Vector

variable {K : Type} [Field K] {n : ℕ}

@[expose] def tvVec (i j : Fin n) : Fin n → K :=
  Pi.single i 1 + Pi.single j 1

@[expose] def tvNil (i j : Fin n) : Matrix (Fin n) (Fin n) K :=
  vecMulVec (tvVec i j) (tvVec i j)

theorem tvVec_apply (i j a : Fin n) :
    tvVec (K := K) i j a = (if a = i then 1 else 0) + (if a = j then 1 else 0) := by
  simp [tvVec, Pi.single_apply]

theorem tvVec_left {i j : Fin n} (hij : i ≠ j) : tvVec (K := K) i j i = 1 := by
  simp [tvVec_apply, hij]

theorem tvVec_right {i j : Fin n} (hij : i ≠ j) : tvVec (K := K) i j j = 1 := by
  simp [tvVec_apply, hij.symm]

omit [Field K] in
theorem ne_left_of_mem_compl {i j a : Fin n} (ha : a ∈ ({i, j}ᶜ : Finset (Fin n))) : a ≠ i := by
  rintro rfl
  simp at ha

omit [Field K] in
theorem ne_right_of_mem_compl {i j a : Fin n} (ha : a ∈ ({i, j}ᶜ : Finset (Fin n))) : a ≠ j := by
  rintro rfl
  simp at ha

omit [Field K] in
theorem mem_compl_of_ne {i j a : Fin n} (hai : a ≠ i) (haj : a ≠ j) :
    a ∈ ({i, j}ᶜ : Finset (Fin n)) := by
  simp [hai, haj]

omit [Field K] in
theorem eq_or_eq_or_mem_compl (i j a : Fin n) :
    a = i ∨ a = j ∨ a ∈ ({i, j}ᶜ : Finset (Fin n)) := by
  by_cases hai : a = i
  · exact Or.inl hai
  · by_cases haj : a = j
    · exact Or.inr (Or.inl haj)
    · exact Or.inr (Or.inr (mem_compl_of_ne hai haj))

theorem tvVec_of_mem_compl {i j a : Fin n} (ha : a ∈ ({i, j}ᶜ : Finset (Fin n))) :
    tvVec (K := K) i j a = 0 := by
  simp [tvVec_apply, ne_left_of_mem_compl ha, ne_right_of_mem_compl ha]

theorem dotProduct_tvVec (i j : Fin n) (x : Fin n → K) : x ⬝ᵥ tvVec i j = x i + x j := by
  rw [tvVec, dotProduct_add, dotProduct_single, dotProduct_single, mul_one, mul_one]

theorem tvVec_dotProduct (i j : Fin n) (x : Fin n → K) : tvVec i j ⬝ᵥ x = x i + x j := by
  rw [tvVec, add_dotProduct, single_dotProduct, single_dotProduct, one_mul, one_mul]

theorem mulVec_tvVec_apply (M : Matrix (Fin n) (Fin n) K) (i j a : Fin n) :
    (M *ᵥ tvVec i j) a = M a i + M a j :=
  dotProduct_tvVec i j _

theorem vecMul_tvVec_apply (M : Matrix (Fin n) (Fin n) K) (i j b : Fin n) :
    (tvVec i j ᵥ* M) b = M i b + M j b :=
  tvVec_dotProduct i j _

theorem tvVec_dotProduct_self [CharP K 2] {i j : Fin n} (hij : i ≠ j) :
    tvVec (K := K) i j ⬝ᵥ tvVec i j = 0 := by
  rw [tvVec_dotProduct, tvVec_left hij, tvVec_right hij, CharTwo.add_self_eq_zero]

theorem sum_eq_sum_compl_add {M : Type*} [AddCommMonoid M] {i j : Fin n} (hij : i ≠ j)
    (g : Fin n → M) :
    ∑ a, g a = ∑ a : ({i, j}ᶜ : Finset (Fin n)), g a + (g i + g j) := by
  rw [← Finset.sum_add_sum_compl ({i, j}ᶜ : Finset (Fin n)) g, compl_compl, Finset.sum_pair hij,
    Finset.sum_coe_sort]

theorem prod_eq_prod_compl_mul {M : Type*} [CommMonoid M] {i j : Fin n} (hij : i ≠ j)
    (g : Fin n → M) :
    ∏ a, g a = (∏ a : ({i, j}ᶜ : Finset (Fin n)), g a) * (g i * g j) := by
  rw [← Finset.prod_mul_prod_compl ({i, j}ᶜ : Finset (Fin n)) g, compl_compl,
    Finset.prod_pair hij, Finset.prod_coe_sort]

end Vector

section Block

variable {K : Type} [Field K] {n : ℕ}

@[expose] def tvBlock (i j : Fin n) (M : Matrix (Fin n) (Fin n) K) :
    Matrix ({i, j}ᶜ : Finset (Fin n)) ({i, j}ᶜ : Finset (Fin n)) K :=
  M.submatrix Subtype.val Subtype.val

omit [Field K] in
theorem tvBlock_apply (i j : Fin n) (M : Matrix (Fin n) (Fin n) K)
    (k l : ({i, j}ᶜ : Finset (Fin n))) : tvBlock i j M k l = M k l :=
  rfl

theorem tvBlock_one (i j : Fin n) : tvBlock i j (1 : Matrix (Fin n) (Fin n) K) = 1 :=
  submatrix_one _ Subtype.val_injective

theorem tvBlock_sub (i j : Fin n) (M M' : Matrix (Fin n) (Fin n) K) :
    tvBlock i j (M - M') = tvBlock i j M - tvBlock i j M' := by
  ext k l
  rfl

theorem apply_eq_one_apply_of_tvBlock_eq_one {i j : Fin n} {M : Matrix (Fin n) (Fin n) K}
    (hM : tvBlock i j M = 1) {k l : Fin n} (hk : k ∈ ({i, j}ᶜ : Finset (Fin n)))
    (hl : l ∈ ({i, j}ᶜ : Finset (Fin n))) : M k l = (1 : Matrix (Fin n) (Fin n) K) k l := by
  have h1 := congrFun (congrFun hM ⟨k, hk⟩) ⟨l, hl⟩
  rw [tvBlock_apply] at h1
  rw [h1]
  by_cases hkl : k = l
  · subst hkl
    rw [one_apply_eq, one_apply_eq]
  · rw [one_apply_ne (fun h' => hkl (congrArg Subtype.val h')), one_apply_ne hkl]

theorem eq_of_mulVec_tvVec [CharP K 2] {i j : Fin n} {M : Matrix (Fin n) (Fin n) K} {μ : K}
    (hM : M *ᵥ tvVec i j = μ • tvVec i j) {k : Fin n} (hk : k ∈ ({i, j}ᶜ : Finset (Fin n))) :
    M k i = M k j := by
  have h1 := congrFun hM k
  rw [mulVec_tvVec_apply, Pi.smul_apply, tvVec_of_mem_compl hk, smul_zero] at h1
  exact CharTwo.add_eq_zero.1 h1

theorem eq_of_vecMul_tvVec [CharP K 2] {i j : Fin n} {M : Matrix (Fin n) (Fin n) K} {μ : K}
    (hM : tvVec i j ᵥ* M = μ • tvVec i j) {l : Fin n} (hl : l ∈ ({i, j}ᶜ : Finset (Fin n))) :
    M i l = M j l := by
  have h1 := congrFun hM l
  rw [vecMul_tvVec_apply, Pi.smul_apply, tvVec_of_mem_compl hl, smul_zero] at h1
  exact CharTwo.add_eq_zero.1 h1

theorem tvBlock_mul [CharP K 2] {i j : Fin n} (hij : i ≠ j) {M M' : Matrix (Fin n) (Fin n) K}
    (hM : ∀ k ∈ ({i, j}ᶜ : Finset (Fin n)), M k i = M k j)
    (hM' : ∀ l ∈ ({i, j}ᶜ : Finset (Fin n)), M' i l = M' j l) :
    tvBlock i j (M * M') = tvBlock i j M * tvBlock i j M' := by
  ext k l
  rw [tvBlock_apply, mul_apply, sum_eq_sum_compl_add hij, hM k k.2, hM' l l.2,
    CharTwo.add_self_eq_zero, add_zero, mul_apply]
  rfl

theorem commute_tvNil_iff {i j : Fin n} (hij : i ≠ j) {M : Matrix (Fin n) (Fin n) K} :
    M * tvNil i j = tvNil i j * M ↔
      ∃ μ : K, M *ᵥ tvVec i j = μ • tvVec i j ∧ tvVec i j ᵥ* M = μ • tvVec i j := by
  rw [tvNil, mul_vecMulVec, vecMulVec_mul]
  constructor
  · intro hc
    have hii := congrFun (congrFun hc i) i
    rw [vecMulVec_apply, vecMulVec_apply, tvVec_left hij, mul_one, one_mul] at hii
    refine ⟨(M *ᵥ tvVec i j) i, ?_, ?_⟩
    · ext a
      have ha := congrFun (congrFun hc a) i
      rw [vecMulVec_apply, vecMulVec_apply, tvVec_left hij, mul_one] at ha
      rw [Pi.smul_apply, smul_eq_mul, ha, hii, mul_comm]
    · ext b
      have hb := congrFun (congrFun hc i) b
      rw [vecMulVec_apply, vecMulVec_apply, tvVec_left hij, one_mul] at hb
      rw [Pi.smul_apply, smul_eq_mul, hb]
  · rintro ⟨μ, h1, h2⟩
    rw [h1, h2, smul_vecMulVec, vecMulVec_smul]

end Block

section Unipotent

variable {K : Type} [Field K] [CharP K 2] {n : ℕ} {i j : Fin n}

theorem mulVec_eq_smul_tvVec (hij : i ≠ j) {X : Matrix (Fin n) (Fin n) K}
    (hXv : X *ᵥ tvVec i j = 0) (hJ : tvBlock i j X = 0) {w : Fin n → K} (hw : w i + w j = 0)
    (hXw : (X *ᵥ w) i + (X *ᵥ w) j = 0) : X *ᵥ w = (X *ᵥ w) i • tvVec i j := by
  ext a
  rw [Pi.smul_apply, smul_eq_mul]
  rcases eq_or_eq_or_mem_compl i j a with rfl | rfl | ha
  · rw [tvVec_left hij, mul_one]
  · rw [tvVec_right hij, mul_one]
    exact (CharTwo.add_eq_zero.1 hXw).symm
  · rw [tvVec_of_mem_compl ha, mul_zero]
    have hai : X a i = X a j := by
      have h1 := congrFun hXv a
      rw [mulVec_tvVec_apply, Pi.zero_apply] at h1
      exact CharTwo.add_eq_zero.1 h1
    have hsum : ∑ b : ({i, j}ᶜ : Finset (Fin n)), X a b * w b = 0 := by
      refine Finset.sum_eq_zero fun b _ => ?_
      have h1 := congrFun (congrFun hJ ⟨a, ha⟩) b
      rw [tvBlock_apply] at h1
      rw [h1, Matrix.zero_apply, zero_mul]
    change ∑ b, X a b * w b = 0
    rw [sum_eq_sum_compl_add hij, hsum, zero_add, hai, ← mul_add,
      show w i + w j = 0 from hw, mul_zero]

theorem pow_three_eq_zero (hij : i ≠ j) {X : Matrix (Fin n) (Fin n) K}
    (hXv : X *ᵥ tvVec i j = 0) (hvX : tvVec i j ᵥ* X = 0) (hJ : tvBlock i j X = 0) :
    X ^ 3 = 0 := by
  have hperp : ∀ u, (X *ᵥ u) i + (X *ᵥ u) j = 0 := fun u => by
    rw [← tvVec_dotProduct, dotProduct_mulVec, hvX, zero_dotProduct]
  refine UnitaryHigher.eq_zero_of_forall_mulVec_eq_zero fun u => ?_
  rw [pow_three, ← mulVec_mulVec, ← mulVec_mulVec,
    mulVec_eq_smul_tvVec hij hXv hJ (hperp u) (hperp _), mulVec_smul, hXv, smul_zero]

theorem sub_one_pow_three_eq_zero_of_tvVec (hij : i ≠ j) {M : Matrix (Fin n) (Fin n) K}
    (h1 : M *ᵥ tvVec i j = tvVec i j) (h2 : tvVec i j ᵥ* M = tvVec i j)
    (h3 : tvBlock i j M = 1) : (M - 1) ^ 3 = 0 :=
  pow_three_eq_zero hij (by rw [sub_mulVec, one_mulVec, h1, sub_self])
    (by rw [vecMul_sub, vecMul_one, h2, sub_self])
    (by rw [tvBlock_sub, h3, tvBlock_one, sub_self])

theorem det_eq_sq (hij : i ≠ j) {M : Matrix (Fin n) (Fin n) K} {μ : K} (hμ : μ ≠ 0)
    (h1 : M *ᵥ tvVec i j = μ • tvVec i j) (h2 : tvVec i j ᵥ* M = μ • tvVec i j)
    (h3 : tvBlock i j M = 1) : M.det = μ ^ 2 := by
  set d : Fin n → K := fun a => if a = i ∨ a = j then μ⁻¹ else 1 with hd
  have hdv : ∀ a, d a * tvVec i j a = μ⁻¹ * tvVec i j a := by
    intro a
    rcases eq_or_eq_or_mem_compl i j a with rfl | rfl | ha
    · simp [hd]
    · simp [hd]
    · rw [tvVec_of_mem_compl ha, mul_zero, mul_zero]
  have hdmv : diagonal d *ᵥ tvVec i j = μ⁻¹ • tvVec i j := by
    ext a
    rw [mulVec_diagonal, hdv, Pi.smul_apply, smul_eq_mul]
  have hvd : tvVec i j ᵥ* diagonal d = μ⁻¹ • tvVec i j := by
    ext a
    rw [vecMul_diagonal, mul_comm, hdv, Pi.smul_apply, smul_eq_mul]
  have hX1 : (M * diagonal d) *ᵥ tvVec i j = tvVec i j := by
    rw [← mulVec_mulVec, hdmv, mulVec_smul, h1, smul_smul, inv_mul_cancel₀ hμ, one_smul]
  have hX2 : tvVec i j ᵥ* (M * diagonal d) = tvVec i j := by
    rw [← vecMul_vecMul, h2, smul_vecMul, hvd, smul_smul, mul_inv_cancel₀ hμ, one_smul]
  have hdJ : tvBlock i j (diagonal d) = 1 := by
    ext k l
    rw [tvBlock_apply]
    by_cases hkl : k = l
    · subst hkl
      have hk : ¬ ((k : Fin n) = i ∨ (k : Fin n) = j) := by
        rintro (h' | h')
        · exact ne_left_of_mem_compl k.2 h'
        · exact ne_right_of_mem_compl k.2 h'
      rw [diagonal_apply_eq, one_apply_eq]
      simp [hd, hk]
    · rw [diagonal_apply_ne _ (fun h' => hkl (Subtype.ext h')), one_apply_ne hkl]
  have hX3 : tvBlock i j (M * diagonal d) = 1 := by
    rw [tvBlock_mul hij (fun k hk => eq_of_mulVec_tvVec h1 hk) (fun l hl => ?_), h3, hdJ,
      Matrix.one_mul]
    rw [diagonal_apply_ne _ (ne_left_of_mem_compl hl).symm,
      diagonal_apply_ne _ (ne_right_of_mem_compl hl).symm]
  have hdet := UnitaryHigher.det_eq_one_of_sub_one_pow_three
    (sub_one_pow_three_eq_zero_of_tvVec hij hX1 hX2 hX3)
  rw [det_mul, det_diagonal, prod_eq_prod_compl_mul hij] at hdet
  have hprod : ∏ a : ({i, j}ᶜ : Finset (Fin n)), d a = 1 := by
    refine Finset.prod_eq_one fun a _ => ?_
    have ha : ¬ ((a : Fin n) = i ∨ (a : Fin n) = j) := by
      rintro (h' | h')
      · exact ne_left_of_mem_compl a.2 h'
      · exact ne_right_of_mem_compl a.2 h'
    simp [hd, ha]
  rw [hprod, one_mul] at hdet
  have hdi : d i = μ⁻¹ := by simp [hd]
  have hdj : d j = μ⁻¹ := by simp [hd]
  rw [hdi, hdj] at hdet
  field_simp at hdet
  linear_combination hdet

end Unipotent

section Elements

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {n : ℕ} {i j : Fin n}

@[expose] noncomputable def tvBar (x : Fin n → K) : Fin n → K :=
  fun k => h.bar (x k)

theorem tvBar_apply (x : Fin n → K) (k : Fin n) : tvBar h x k = h.bar (x k) :=
  rfl

theorem tvBar_add (x y : Fin n → K) : tvBar h (x + y) = tvBar h x + tvBar h y := by
  ext k
  simp [tvBar, map_add]

theorem tvBar_zero : tvBar h (0 : Fin n → K) = 0 := by
  ext k
  simp [tvBar]

theorem bar_tvVec (i j a : Fin n) : h.bar (tvVec (K := K) i j a) = tvVec i j a := by
  rw [tvVec_apply, map_add]
  split_ifs <;> simp

theorem tvBar_dotProduct_tvVec {x : Fin n → K} (hxi : x i = 0) (hxj : x j = 0) :
    tvBar h x ⬝ᵥ tvVec i j = 0 := by
  rw [dotProduct_tvVec, tvBar_apply, tvBar_apply, hxi, hxj, map_zero, add_zero]

theorem tvVec_dotProduct_of_eq_zero {x : Fin n → K} (hxi : x i = 0) (hxj : x j = 0) :
    tvVec i j ⬝ᵥ x = 0 := by
  rw [tvVec_dotProduct, hxi, hxj, add_zero]

variable (i j) in
@[expose] noncomputable def tvE (x : Fin n → K) (s : K) : Matrix (Fin n) (Fin n) K :=
  1 + s • tvNil i j + vecMulVec x (tvVec i j) + vecMulVec (tvVec i j) (tvBar h x)

theorem tvE_apply (x : Fin n → K) (s : K) (a b : Fin n) :
    tvE h i j x s a b = (1 : Matrix (Fin n) (Fin n) K) a b + s * (tvVec i j a * tvVec i j b) +
      x a * tvVec i j b + tvVec i j a * h.bar (x b) :=
  rfl

theorem tvE_zero_zero : tvE h i j 0 0 = 1 := by
  simp [tvE, tvBar_zero]

theorem tvE_mul (hij : i ≠ j) {x x' : Fin n → K} (hxi : x i = 0) (hxj : x j = 0)
    (hx'i : x' i = 0) (hx'j : x' j = 0) (s s' : K) :
    tvE h i j x s * tvE h i j x' s' = tvE h i j (x + x') (s + s' + tvBar h x ⬝ᵥ x') := by
  have := h.charP
  have hvv : tvVec i j ⬝ᵥ tvVec i j = (0 : K) := tvVec_dotProduct_self hij
  have hvx' := tvVec_dotProduct_of_eq_zero (i := i) (j := j) hx'i hx'j
  have hbxv := tvBar_dotProduct_tvVec h hxi hxj
  simp only [tvE, tvNil, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, vecMulVec_mul_vecMulVec, hvv, hvx', hbxv, zero_smul,
    vecMulVec_zero, smul_zero, add_zero, tvBar_add, add_vecMulVec, vecMulVec_add, add_smul,
    vecMulVec_smul]
  abel

theorem tvE_mulVec_tvVec (hij : i ≠ j) {x : Fin n → K} (hxi : x i = 0) (hxj : x j = 0)
    (s : K) : tvE h i j x s *ᵥ tvVec i j = tvVec i j := by
  have := h.charP
  simp only [tvE, tvNil, add_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec,
    tvVec_dotProduct_self hij, tvBar_dotProduct_tvVec h hxi hxj, MulOpposite.op_zero,
    zero_smul, smul_zero, add_zero]

theorem vecMul_tvE (hij : i ≠ j) {x : Fin n → K} (hxi : x i = 0) (hxj : x j = 0) (s : K) :
    tvVec i j ᵥ* tvE h i j x s = tvVec i j := by
  have := h.charP
  simp only [tvE, tvNil, vecMul_add, vecMul_one, vecMul_smul, vecMul_vecMulVec,
    tvVec_dotProduct_self hij, tvVec_dotProduct_of_eq_zero hxi hxj, zero_smul, smul_zero,
    add_zero]

theorem tvBlock_tvE (x : Fin n → K) (s : K) : tvBlock i j (tvE h i j x s) = 1 := by
  ext k l
  rw [tvBlock_apply, tvE_apply, tvVec_of_mem_compl k.2, tvVec_of_mem_compl l.2]
  simp only [mul_zero, zero_mul, add_zero]
  by_cases hkl : k = l
  · subst hkl
    rw [one_apply_eq, one_apply_eq]
  · rw [one_apply_ne (fun h' => hkl (Subtype.ext h')), one_apply_ne hkl]

theorem tvE_sub_one_pow_three (hij : i ≠ j) {x : Fin n → K} (hxi : x i = 0) (hxj : x j = 0)
    (s : K) : (tvE h i j x s - 1) ^ 3 = 0 := by
  have := h.charP
  exact sub_one_pow_three_eq_zero_of_tvVec hij (tvE_mulVec_tvVec h hij hxi hxj s)
    (vecMul_tvE h hij hxi hxj s) (tvBlock_tvE h x s)

theorem det_tvE (hij : i ≠ j) {x : Fin n → K} (hxi : x i = 0) (hxj : x j = 0) (s : K) :
    (tvE h i j x s).det = 1 :=
  UnitaryHigher.det_eq_one_of_sub_one_pow_three (tvE_sub_one_pow_three h hij hxi hxj s)

theorem barTranspose_tvE (x : Fin n → K) (s : K) :
    ((tvE h i j x s).map h.bar)ᵀ = tvE h i j x (h.bar s) := by
  ext a b
  rw [transpose_apply, map_apply, tvE_apply, tvE_apply]
  simp only [map_add, map_mul, bar_tvVec, h.bar_bar]
  rw [show h.bar ((1 : Matrix (Fin n) (Fin n) K) b a) = (1 : Matrix (Fin n) (Fin n) K) a b by
    by_cases hab : a = b
    · subst hab
      rw [one_apply_eq, map_one]
    · rw [one_apply_ne (Ne.symm hab), one_apply_ne hab, map_zero]]
  ring

theorem barTranspose_tvE_mul_self (hij : i ≠ j) {x : Fin n → K} (hxi : x i = 0)
    (hxj : x j = 0) {s : K} (hs : s + h.bar s = tvBar h x ⬝ᵥ x) :
    ((tvE h i j x s).map h.bar)ᵀ * tvE h i j x s = 1 := by
  have := h.charP
  rw [barTranspose_tvE, tvE_mul h hij hxi hxj hxi hxj]
  have h0 : x + x = 0 := by
    ext k
    exact CharTwo.add_self_eq_zero _
  have h1 : h.bar s + s + tvBar h x ⬝ᵥ x = 0 := by
    rw [add_comm (h.bar s), hs, CharTwo.add_self_eq_zero]
  rw [h0, h1, tvE_zero_zero]

theorem mul_tvE {m : Matrix (Fin n) (Fin n) K} (hm1 : m *ᵥ tvVec i j = tvVec i j)
    (hm2 : tvVec i j ᵥ* m = tvVec i j) (hmu : (m.map h.bar)ᵀ * m = 1) (x : Fin n → K)
    (s : K) : m * tvE h i j x s = tvE h i j (m *ᵥ x) s * m := by
  have hbx : tvBar h (m *ᵥ x) ᵥ* m = tvBar h x := by
    have e1 : tvBar h (m *ᵥ x) = m.map h.bar *ᵥ tvBar h x :=
      funext fun k => RingHom.map_mulVec h.bar m x k
    rw [e1, ← vecMul_transpose, vecMul_vecMul, hmu, vecMul_one]
  simp only [tvE, tvNil, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_smul, Matrix.smul_mul, mul_vecMulVec, vecMulVec_mul, hm1, hm2, hbx]

theorem eq_tvE_of_unitary (hij : i ≠ j) {r : Matrix (Fin n) (Fin n) K}
    (hu : (r.map h.bar)ᵀ * r = 1) (h1 : r *ᵥ tvVec i j = tvVec i j)
    (h2 : tvVec i j ᵥ* r = tvVec i j) (h3 : tvBlock i j r = 1) :
    ∃ x : Fin n → K, x i = 0 ∧ x j = 0 ∧
      ∃ s : K, s + h.bar s = tvBar h x ⬝ᵥ x ∧ r = tvE h i j x s := by
  have := h.charP
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  set x : Fin n → K := fun a => if a = i ∨ a = j then 0 else r a i with hx
  have hxi : x i = 0 := by simp [hx]
  have hxj : x j = 0 := by simp [hx]
  have hxa : ∀ a ∈ ({i, j}ᶜ : Finset (Fin n)), x a = r a i := fun a ha => by
    simp [hx, ne_left_of_mem_compl ha, ne_right_of_mem_compl ha]
  have F1 : ∀ a, r a i + r a j = tvVec i j a := fun a => by
    rw [← mulVec_tvVec_apply, h1]
  have F2 : ∀ b, r i b + r j b = tvVec i j b := fun b => by
    rw [← vecMul_tvVec_apply, h2]
  have hU : ∀ a b, ∑ c, h.bar (r c a) * r c b = (1 : Matrix (Fin n) (Fin n) K) a b :=
    fun a b => by
      have h4 := congrFun (congrFun hu a) b
      rw [mul_apply] at h4
      exact h4
  have F4 : ∀ l ∈ ({i, j}ᶜ : Finset (Fin n)), r i l = h.bar (r l i) := by
    intro l hl
    have hrjl : r j l = r i l := by
      have h4 := F2 l
      rw [tvVec_of_mem_compl hl] at h4
      exact (CharTwo.add_eq_zero.1 h4).symm
    have hsum : ∑ c : ({i, j}ᶜ : Finset (Fin n)), h.bar (r c l) * r c i = r l i := by
      rw [Finset.sum_eq_single (⟨l, hl⟩ : ({i, j}ᶜ : Finset (Fin n)))]
      · rw [apply_eq_one_apply_of_tvBlock_eq_one h3 hl hl, one_apply_eq, map_one, one_mul]
      · intro c _ hc
        rw [apply_eq_one_apply_of_tvBlock_eq_one h3 c.2 hl,
          one_apply_ne (fun h' => hc (Subtype.ext h')), map_zero, zero_mul]
      · intro h'
        exact absurd (Finset.mem_univ _) h'
    have h4 := hU l i
    rw [sum_eq_sum_compl_add hij, hsum, hrjl, ← mul_add, F2 i, tvVec_left hij, mul_one,
      one_apply_ne (ne_left_of_mem_compl hl)] at h4
    rw [CharTwo.add_eq_zero.1 h4, h.bar_bar]
  set s := r i j with hs
  have hrii : r i i = 1 + s := by
    have h4 := F1 i
    rw [tvVec_left hij] at h4
    linear_combination h4 - r i j * h2K
  have hrji : r j i = s := by
    have h4 := F2 i
    rw [tvVec_left hij, hrii] at h4
    linear_combination h4 - s * h2K
  have hrjj : r j j = 1 + s := by
    have h4 := F1 j
    rw [tvVec_right hij, hrji] at h4
    linear_combination h4 - s * h2K
  refine ⟨x, hxi, hxj, s, ?_, ?_⟩
  ·
    have h4 := hU i i
    rw [sum_eq_sum_compl_add hij, hrii, hrji, one_apply_eq] at h4
    have h5 : tvBar h x ⬝ᵥ x = ∑ c : ({i, j}ᶜ : Finset (Fin n)), h.bar (r c i) * r c i := by
      change ∑ c, h.bar (x c) * x c = _
      rw [sum_eq_sum_compl_add hij, hxi, hxj, map_zero, zero_mul, add_zero, add_zero]
      exact Finset.sum_congr rfl fun c _ => by rw [hxa c c.2]
    rw [h5]
    simp only [map_add, map_one] at h4
    linear_combination (-1 : K) * h4 + (s + h.bar s + h.bar s * s) * h2K
  ·
    have colJ : ∀ b ∈ ({i, j}ᶜ : Finset (Fin n)), ∀ a, r a b = tvE h i j x s a b := by
      intro b hb a
      rw [tvE_apply, tvVec_of_mem_compl hb, hxa b hb]
      simp only [mul_zero, add_zero]
      rcases eq_or_eq_or_mem_compl i j a with ha | ha | ha
      · rw [ha, tvVec_left hij, one_apply_ne (ne_left_of_mem_compl hb).symm, F4 b hb]
        ring
      · have h4 := F2 b
        rw [tvVec_of_mem_compl hb] at h4
        rw [ha, tvVec_right hij, one_apply_ne (ne_right_of_mem_compl hb).symm,
          ← (CharTwo.add_eq_zero.1 h4), F4 b hb]
        ring
      · rw [tvVec_of_mem_compl ha, zero_mul, add_zero]
        exact apply_eq_one_apply_of_tvBlock_eq_one h3 ha hb
    have coli : ∀ a, r a i = tvE h i j x s a i := by
      intro a
      rw [tvE_apply, tvVec_left hij, hxi, map_zero, mul_zero, add_zero, mul_one, mul_one]
      rcases eq_or_eq_or_mem_compl i j a with ha | ha | ha
      · rw [ha, hrii, one_apply_eq, tvVec_left hij, hxi, mul_one, add_zero]
      · rw [ha, hrji, one_apply_ne hij.symm, tvVec_right hij, hxj, mul_one, add_zero, zero_add]
      · rw [one_apply_ne (ne_left_of_mem_compl ha), tvVec_of_mem_compl ha, hxa a ha, mul_zero,
          zero_add, zero_add]
    have colj : ∀ a, r a j = tvE h i j x s a j := by
      intro a
      rw [tvE_apply, tvVec_right hij, hxj, map_zero, mul_zero, add_zero, mul_one, mul_one]
      rcases eq_or_eq_or_mem_compl i j a with ha | ha | ha
      · rw [ha, one_apply_ne hij, tvVec_left hij, hxi, mul_one, add_zero, zero_add]
      · rw [ha, hrjj, one_apply_eq, tvVec_right hij, hxj, mul_one, add_zero]
      · have h4 := F1 a
        rw [tvVec_of_mem_compl ha] at h4
        rw [one_apply_ne (ne_right_of_mem_compl ha), tvVec_of_mem_compl ha, hxa a ha, mul_zero,
          zero_add, zero_add, ← CharTwo.add_eq_zero.1 h4]
    ext a b
    rcases eq_or_eq_or_mem_compl i j b with hb | hb | hb
    · rw [hb]
      exact coli a
    · rw [hb]
      exact colj a
    · exact colJ b hb a

end Elements

end CFSG.SeitzReduction.UnitaryPilot
