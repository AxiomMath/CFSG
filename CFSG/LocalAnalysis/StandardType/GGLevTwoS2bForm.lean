module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS2bCoord

public section

namespace CFSG.StandardType.LevTwo

open CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin
open scoped Matrix

@[expose] def levTwoS2b_last (n : ℕ) (hn : 1 ≤ n) : Fin n := ⟨n - 1, by omega⟩

@[expose] noncomputable def levTwoS2b_kappa (n : ℕ) (hn : 1 ≤ n) : ℚ :=
  2 * symmetrizer (isFiniteType_cartanB n) (levTwoS2b_last n hn)

theorem levTwoS2b_kappa_pos (n : ℕ) (hn : 1 ≤ n) : 0 < levTwoS2b_kappa n hn := by
  rw [levTwoS2b_kappa]
  exact mul_pos (by norm_num) (symmetrizer_pos (isFiniteType_cartanB n) (levTwoS2b_last n hn))

@[expose] def levTwoS2b_coordLin (n : ℕ) : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ) where
  toFun := levTwoS2b_coord n
  map_add' := levTwoS2b_coord_add n
  map_smul' := levTwoS2b_coord_smul n

theorem levTwoS2b_coord_eq_sum (n : ℕ) (u : Fin n → ℤ) :
    levTwoS2b_coord n u = ∑ i : Fin n, u i • levTwoS2b_coord n (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single u]
  change levTwoS2b_coordLin n (∑ i : Fin n, Pi.single i (u i)) =
    ∑ i : Fin n, u i • levTwoS2b_coord n (Pi.single i 1)
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show Pi.single i (u i) = u i • (Pi.single i 1 : Fin n → ℤ) by
    funext k; by_cases hk : k = i <;> simp [hk]]
  rw [map_smul]
  rfl

theorem levTwoS2b_form_single_single (n : ℕ) (i j : Fin n) :
    form (isFiniteType_cartanB n) (toRat (Pi.single i 1)) (toRat (Pi.single j 1)) =
      symmetrizer (isFiniteType_cartanB n) i * (cartanB n i j : ℚ) := by
  rw [toRat_single, toRat_single, form_single_left]
  congr 1
  rw [Fintype.sum_eq_single j]
  · simp
  · intro k hk
    simp [hk]

theorem levTwoS2b_symmetrizer_mul_eq (n : ℕ) (i j : Fin n) :
    symmetrizer (isFiniteType_cartanB n) i * (cartanB n i j : ℚ) =
      symmetrizer (isFiniteType_cartanB n) j * (cartanB n j i : ℚ) := by
  have h := form_comm (isFiniteType_cartanB n) (toRat (Pi.single i 1)) (toRat (Pi.single j 1))
  rwa [levTwoS2b_form_single_single, levTwoS2b_form_single_single] at h

theorem levTwoS2b_cartanB_succ (n : ℕ) {i : Fin n} (h : i.val + 1 < n) :
    cartanB n i ⟨i.val + 1, h⟩ = -1 := by
  have hne : (i : Fin n) ≠ ⟨i.val + 1, h⟩ := by
    intro he
    have hv := congrArg Fin.val he
    simp only at hv
    omega
  have hadj : i.val + 1 = (⟨i.val + 1, h⟩ : Fin n).val ∨
      (⟨i.val + 1, h⟩ : Fin n).val + 1 = i.val :=
    Or.inl (by simp only)
  have hnot : ¬ (i.val + 1 = n ∧ (⟨i.val + 1, h⟩ : Fin n).val + 2 = n) := by
    simp only
    omega
  rw [cartanB, Matrix.of_apply, if_neg hne, if_pos hadj, if_neg hnot]

theorem levTwoS2b_cartanB_pred (n : ℕ) {i : Fin n} (h : i.val + 1 < n) :
    cartanB n ⟨i.val + 1, h⟩ i = if i.val + 2 = n then -2 else -1 := by
  have hne : (⟨i.val + 1, h⟩ : Fin n) ≠ i := by
    intro he
    have hv := congrArg Fin.val he
    simp only at hv
    omega
  have hadj : (⟨i.val + 1, h⟩ : Fin n).val + 1 = i.val ∨
      i.val + 1 = (⟨i.val + 1, h⟩ : Fin n).val :=
    Or.inr (by simp only)
  rw [cartanB, Matrix.of_apply, if_neg hne, if_pos hadj]
  by_cases hi : i.val + 2 = n
  · rw [if_pos (by simp only; omega), if_pos hi]
  · rw [if_neg (by simp only; omega), if_neg hi]

theorem levTwoS2b_symmetrizer_step (n : ℕ) {i : Fin n} (h : i.val + 1 < n)
    (h2 : i.val + 2 < n) :
    symmetrizer (isFiniteType_cartanB n) i =
      symmetrizer (isFiniteType_cartanB n) ⟨i.val + 1, h⟩ := by
  have hs := levTwoS2b_symmetrizer_mul_eq n i ⟨i.val + 1, h⟩
  rw [levTwoS2b_cartanB_succ n h, levTwoS2b_cartanB_pred n h, if_neg (by omega)] at hs
  norm_num at hs
  linarith

theorem levTwoS2b_symmetrizer_last (n : ℕ) {i : Fin n} (h : i.val + 1 < n)
    (h2 : i.val + 2 = n) :
    symmetrizer (isFiniteType_cartanB n) i =
      2 * symmetrizer (isFiniteType_cartanB n) ⟨i.val + 1, h⟩ := by
  have hs := levTwoS2b_symmetrizer_mul_eq n i ⟨i.val + 1, h⟩
  rw [levTwoS2b_cartanB_succ n h, levTwoS2b_cartanB_pred n h, if_pos h2] at hs
  norm_num at hs
  linarith

theorem levTwoS2b_eq_last_of_not_lt (n : ℕ) (hn : 1 ≤ n) {i : Fin n}
    (hi : ¬ i.val + 1 < n) : i = levTwoS2b_last n hn :=
  Fin.ext (by rw [levTwoS2b_last]; simp only; omega)

theorem levTwoS2b_symmetrizer_eq_half (n : ℕ) (hn : 1 ≤ n) :
    symmetrizer (isFiniteType_cartanB n) (levTwoS2b_last n hn) = levTwoS2b_kappa n hn / 2 := by
  rw [levTwoS2b_kappa]
  ring

theorem levTwoS2b_symmetrizer_eq_kappa_aux (n : ℕ) (hn : 1 ≤ n) (m : ℕ) :
    ∀ i : Fin n, i.val + m = n - 2 → i.val + 1 < n →
      symmetrizer (isFiniteType_cartanB n) i = levTwoS2b_kappa n hn := by
  induction m with
  | zero =>
      intro i hi hlong
      have h2 : i.val + 2 = n := by omega
      rw [levTwoS2b_symmetrizer_last n hlong h2]
      have hlast : (⟨i.val + 1, hlong⟩ : Fin n) = levTwoS2b_last n hn := by
        apply Fin.ext
        rw [levTwoS2b_last]
        simp only
        omega
      rw [hlast, levTwoS2b_symmetrizer_eq_half n hn, levTwoS2b_kappa]
      ring
  | succ m ih =>
      intro i hi hlong
      have h2 : i.val + 2 < n := by omega
      rw [levTwoS2b_symmetrizer_step n hlong h2]
      exact ih ⟨i.val + 1, hlong⟩ (by simp only; omega) (by simp only; omega)

theorem levTwoS2b_symmetrizer_eq_kappa (n : ℕ) (hn : 1 ≤ n) {i : Fin n} (hi : i.val + 1 < n) :
    symmetrizer (isFiniteType_cartanB n) i = levTwoS2b_kappa n hn :=
  levTwoS2b_symmetrizer_eq_kappa_aux n hn (n - 2 - i.val) i (by omega) hi

theorem levTwoS2b_single_mul_single (n : ℕ) (a b : Fin n) :
    ∑ k : Fin n, ((Pi.single a (1 : ℤ) : Fin n → ℤ) k : ℚ) *
        ((Pi.single b (1 : ℤ) : Fin n → ℤ) k : ℚ) = if a = b then 1 else 0 := by
  by_cases hab : a = b
  · subst hab
    rw [Fintype.sum_eq_single a]
    · simp
    · intro k hk
      simp [hk]
  · rw [Fintype.sum_eq_single a]
    · simp [hab]
    · intro k hk
      simp [Pi.single_apply, hk]

theorem levTwoS2b_cartanB_of_long (n : ℕ) {i j : Fin n} (hi : i.val + 1 < n) (hij : i ≠ j) :
    cartanB n i j = if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1 else 0 := by
  rw [cartanB, Matrix.of_apply, if_neg hij]
  by_cases hadj : i.val + 1 = j.val ∨ j.val + 1 = i.val
  · have hinner : ¬ (i.val + 1 = n ∧ j.val + 2 = n) := by intro hc; omega
    rw [if_pos hadj, if_neg hinner, if_pos hadj]
  · rw [if_neg hadj, if_neg hadj]

theorem levTwoS2b_gram_eq (n : ℕ) (i j : Fin n) :
    ∑ k : Fin n, ((levTwoS2b_coord n (Pi.single i 1) k : ℤ) : ℚ) *
        ((levTwoS2b_coord n (Pi.single j 1) k : ℤ) : ℚ) =
      if i = j then (if i.val + 1 < n then 2 else 1)
      else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1 else 0 := by
  simp only [levTwoS2b_coord]
  by_cases hi : i.val + 1 < n
  · rw [CFSG.LieType.Universal.Spin.toStdB_single_of_lt n hi]
    by_cases hj : j.val + 1 < n
    · rw [CFSG.LieType.Universal.Spin.toStdB_single_of_lt n hj]
      simp only [Pi.sub_apply, Int.cast_sub, sub_mul, mul_sub, Finset.sum_sub_distrib]
      rw [levTwoS2b_single_mul_single, levTwoS2b_single_mul_single,
          levTwoS2b_single_mul_single, levTwoS2b_single_mul_single]
      rw [if_pos hi]
      simp only [Fin.ext_iff]
      by_cases h1 : i.val = j.val
      · have h2 : ¬ (i.val = j.val + 1) := by omega
        have h3 : ¬ (i.val + 1 = j.val) := by omega
        have h4 : i.val + 1 = j.val + 1 := by omega
        have h5 : ¬ (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by omega
        simp only [if_pos h1, if_neg h2, if_neg h3, if_pos h4, if_neg h5]
        norm_num
      · by_cases h2 : i.val + 1 = j.val
        · have h3 : ¬ (i.val = j.val + 1) := by omega
          have h4 : ¬ (i.val + 1 = j.val + 1) := by omega
          have h5 : i.val + 1 = j.val ∨ j.val + 1 = i.val := Or.inl h2
          simp only [if_neg h1, if_neg h3, if_pos h2, if_neg h4, if_pos h5]
          norm_num
        · by_cases h3 : i.val = j.val + 1
          · have h4 : ¬ (i.val + 1 = j.val + 1) := by omega
            have h5 : i.val + 1 = j.val ∨ j.val + 1 = i.val := Or.inr (by omega)
            simp only [if_neg h1, if_neg h2, if_pos h3, if_neg h4, if_pos h5]
            norm_num
          · have h4 : ¬ (i.val + 1 = j.val + 1) := by omega
            have h5 : ¬ (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by omega
            simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5]
            norm_num
    · rw [CFSG.LieType.Universal.Spin.toStdB_single_of_not_lt n hj]
      simp only [Pi.sub_apply, Int.cast_sub, sub_mul, Finset.sum_sub_distrib]
      rw [levTwoS2b_single_mul_single, levTwoS2b_single_mul_single]
      rw [if_pos hi]
      simp only [Fin.ext_iff]
      have hjval : j.val = n - 1 := by omega
      have h1 : ¬ (i.val = j.val) := by omega
      by_cases h2 : i.val + 1 = j.val
      · have h5 : i.val + 1 = j.val ∨ j.val + 1 = i.val := Or.inl h2
        simp only [if_neg h1, if_pos h2, if_pos h5]
        norm_num
      · have h5 : ¬ (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by omega
        simp only [if_neg h1, if_neg h2, if_neg h5]
        norm_num
  · rw [CFSG.LieType.Universal.Spin.toStdB_single_of_not_lt n hi]
    by_cases hj : j.val + 1 < n
    · rw [CFSG.LieType.Universal.Spin.toStdB_single_of_lt n hj]
      simp only [Pi.sub_apply, Int.cast_sub, mul_sub, Finset.sum_sub_distrib]
      rw [levTwoS2b_single_mul_single, levTwoS2b_single_mul_single]
      rw [if_neg hi]
      simp only [Fin.ext_iff]
      have h1 : ¬ (i.val = j.val) := by omega
      by_cases h3 : i.val = j.val + 1
      · have h5 : i.val + 1 = j.val ∨ j.val + 1 = i.val := Or.inr (by omega)
        simp only [if_neg h1, if_pos h3, if_pos h5]
        norm_num
      · have h5 : ¬ (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by omega
        simp only [if_neg h1, if_neg h3, if_neg h5]
        norm_num
    · rw [CFSG.LieType.Universal.Spin.toStdB_single_of_not_lt n hj]
      rw [levTwoS2b_single_mul_single]
      rw [if_neg hi]
      have hij : i = j := by apply Fin.ext; omega
      simp only [if_pos hij]

theorem levTwoS2b_entry (n : ℕ) (hn : 1 ≤ n) (i j : Fin n) :
    symmetrizer (isFiniteType_cartanB n) i * (cartanB n i j : ℚ) =
      levTwoS2b_kappa n hn *
        ∑ k : Fin n, ((levTwoS2b_coord n (Pi.single i 1) k : ℤ) : ℚ) *
          ((levTwoS2b_coord n (Pi.single j 1) k : ℤ) : ℚ) := by
  rw [levTwoS2b_gram_eq n i j]
  rcases eq_or_ne i j with rfl | hij
  · by_cases hi : i.val + 1 < n
    · rw [if_pos rfl, if_pos hi, levTwoS2b_symmetrizer_eq_kappa n hn hi,
        (isFiniteType_cartanB n).apply_self i]
      norm_num
    · rw [if_pos rfl, if_neg hi, levTwoS2b_eq_last_of_not_lt n hn hi,
        levTwoS2b_symmetrizer_eq_half n hn, (isFiniteType_cartanB n).apply_self]
      ring
  · rw [if_neg hij]
    by_cases hi : i.val + 1 < n
    · rw [levTwoS2b_symmetrizer_eq_kappa n hn hi, levTwoS2b_cartanB_of_long n hi hij]
      by_cases hp : i.val + 1 = j.val ∨ j.val + 1 = i.val <;> simp [hp]
    · have hsym := levTwoS2b_symmetrizer_mul_eq n i j
      have hj : j.val + 1 < n := by
        by_contra hj
        exact hij ((levTwoS2b_eq_last_of_not_lt n hn hi).trans
          (levTwoS2b_eq_last_of_not_lt n hn hj).symm)
      rw [levTwoS2b_symmetrizer_eq_kappa n hn hj] at hsym
      rw [levTwoS2b_cartanB_of_long n hj (Ne.symm hij)] at hsym
      rw [hsym]
      simp only [or_comm]
      by_cases hp : i.val + 1 = j.val ∨ j.val + 1 = i.val <;> simp [hp]

theorem levTwoS2b_coord_apply_sum (n : ℕ) (u : Fin n → ℤ) (m : Fin n) :
    ((levTwoS2b_coord n u m : ℤ) : ℚ) =
      ∑ i : Fin n, ((u i : ℤ) : ℚ) *
        ((levTwoS2b_coord n (Pi.single i 1) m : ℤ) : ℚ) := by
  have h := congrFun (levTwoS2b_coord_eq_sum n u) m
  rw [h]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul]

theorem levTwoS2b_sum_rearrange (n : ℕ) (u v : Fin n → ℤ) :
    ∑ i : Fin n, ((u i : ℤ) : ℚ) *
        (∑ j : Fin n, ((v j : ℤ) : ℚ) *
          (∑ m : Fin n, ((levTwoS2b_coord n (Pi.single i 1) m : ℤ) : ℚ) *
            ((levTwoS2b_coord n (Pi.single j 1) m : ℤ) : ℚ))) =
      ∑ m : Fin n, ((levTwoS2b_coord n u m : ℤ) : ℚ) *
        ((levTwoS2b_coord n v m : ℤ) : ℚ) := by
  simp only [levTwoS2b_coord_apply_sum n u, levTwoS2b_coord_apply_sum n v]
  set M : Fin n → Fin n → ℚ :=
    fun i m => ((levTwoS2b_coord n (Pi.single i 1) m : ℤ) : ℚ)
  have e1 : (∑ i : Fin n, ((u i : ℤ) : ℚ) *
        (∑ j : Fin n, ((v j : ℤ) : ℚ) * (∑ m : Fin n, M i m * M j m))) =
      ∑ i : Fin n, ∑ j : Fin n, ∑ m : Fin n,
        ((u i : ℤ) : ℚ) * (((v j : ℤ) : ℚ) * (M i m * M j m)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    rw [Finset.mul_sum]
  have e2 : (∑ m : Fin n, (∑ i : Fin n, ((u i : ℤ) : ℚ) * M i m) *
        (∑ j : Fin n, ((v j : ℤ) : ℚ) * M j m)) =
      ∑ m : Fin n, ∑ i : Fin n, ∑ j : Fin n,
        (((u i : ℤ) : ℚ) * M i m) * (((v j : ℤ) : ℚ) * M j m) := by
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_mul_sum]
  rw [e1, e2]
  rw [show (∑ i : Fin n, ∑ j : Fin n, ∑ m : Fin n,
        ((u i : ℤ) : ℚ) * (((v j : ℤ) : ℚ) * (M i m * M j m))) =
      ∑ i : Fin n, ∑ m : Fin n, ∑ j : Fin n,
        ((u i : ℤ) : ℚ) * (((v j : ℤ) : ℚ) * (M i m * M j m))
      from Finset.sum_congr rfl fun i _ => Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem levTwoS2b_kappa_factor (n : ℕ) (hn : 1 ≤ n) (u v : Fin n → ℤ) :
    ∑ i : Fin n, ((u i : ℤ) : ℚ) *
        (∑ j : Fin n, ((v j : ℤ) : ℚ) *
          (levTwoS2b_kappa n hn *
            ∑ m : Fin n, ((levTwoS2b_coord n (Pi.single i 1) m : ℤ) : ℚ) *
              ((levTwoS2b_coord n (Pi.single j 1) m : ℤ) : ℚ))) =
      levTwoS2b_kappa n hn *
        ∑ i : Fin n, ((u i : ℤ) : ℚ) *
          (∑ j : Fin n, ((v j : ℤ) : ℚ) *
            (∑ m : Fin n, ((levTwoS2b_coord n (Pi.single i 1) m : ℤ) : ℚ) *
              ((levTwoS2b_coord n (Pi.single j 1) m : ℤ) : ℚ))) := by
  conv_rhs => rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_lhs => rw [Finset.mul_sum]
  conv_rhs => rw [Finset.mul_sum]
  conv_rhs => rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem levTwoS2b_form_coord_kappa (n : ℕ) (hn : 1 ≤ n) (u v : Fin n → ℤ) :
    form (isFiniteType_cartanB n) (toRat u) (toRat v) =
      levTwoS2b_kappa n hn * ∑ k : Fin n, ((levTwoS2b_coord n u k : ℤ) : ℚ) *
        ((levTwoS2b_coord n v k : ℤ) : ℚ) := by
  have hleft : form (isFiniteType_cartanB n) (toRat u) (toRat v) =
      ∑ i : Fin n, ((u i : ℤ) : ℚ) *
        form (isFiniteType_cartanB n) (Pi.single i (1 : ℚ)) (toRat v) := by
    rw [form_comm, form_eq_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [toRat_apply, form_comm]
  rw [hleft]
  have hterm : ∀ i : Fin n,
      form (isFiniteType_cartanB n) (Pi.single i (1 : ℚ)) (toRat v) =
        ∑ j : Fin n, ((v j : ℤ) : ℚ) *
          (levTwoS2b_kappa n hn *
            ∑ m : Fin n, ((levTwoS2b_coord n (Pi.single i 1) m : ℤ) : ℚ) *
              ((levTwoS2b_coord n (Pi.single j 1) m : ℤ) : ℚ)) := by
    intro i
    rw [form_single_left, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_assoc, levTwoS2b_entry n hn i j, toRat_apply]
    ring
  rw [show (∑ i : Fin n, ((u i : ℤ) : ℚ) *
        form (isFiniteType_cartanB n) (Pi.single i (1 : ℚ)) (toRat v)) =
      ∑ i : Fin n, ((u i : ℤ) : ℚ) *
        (∑ j : Fin n, ((v j : ℤ) : ℚ) *
          (levTwoS2b_kappa n hn *
            ∑ m : Fin n, ((levTwoS2b_coord n (Pi.single i 1) m : ℤ) : ℚ) *
              ((levTwoS2b_coord n (Pi.single j 1) m : ℤ) : ℚ)))
      from Finset.sum_congr rfl fun i _ => by rw [hterm i]]
  rw [levTwoS2b_kappa_factor n hn u v, levTwoS2b_sum_rearrange n u v]

end CFSG.StandardType.LevTwo
