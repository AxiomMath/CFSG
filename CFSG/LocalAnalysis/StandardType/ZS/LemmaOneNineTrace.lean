module

public import CFSG.LocalAnalysis.StandardType.ZS.LemmaOneNineMatrix

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime]

private lemma ch2 (M : Matrix (Fin 2) (Fin 2) (ZMod p)) :
    M ^ 2 = M.trace • M - M.det • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, Matrix.mul_apply, Matrix.trace_fin_two, Matrix.det_fin_two,
      Fin.sum_univ_two, Matrix.smul_apply] <;> ring

private lemma mat_pow_three (M : Matrix (Fin 2) (Fin 2) (ZMod p)) :
    M ^ 3 = (M.trace ^ 2 - M.det) • M - (M.trace * M.det) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Matrix.trace_fin_two, Matrix.det_fin_two,
      Fin.sum_univ_two, Matrix.smul_apply] <;> ring

private lemma mat_pow_four (M : Matrix (Fin 2) (Fin 2) (ZMod p)) :
    M ^ 4 = (M.trace ^ 3 - 2 * M.trace * M.det) • M
      + (M.det ^ 2 - M.trace ^ 2 * M.det) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Matrix.trace_fin_two, Matrix.det_fin_two,
      Fin.sum_univ_two, Matrix.smul_apply] <;> ring

private lemma mat_pow_five (M : Matrix (Fin 2) (Fin 2) (ZMod p)) :
    M ^ 5 = (M.trace ^ 4 - 3 * M.trace ^ 2 * M.det + M.det ^ 2) • M
      + (2 * M.trace * M.det ^ 2 - M.trace ^ 3 * M.det) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Matrix.trace_fin_two, Matrix.det_fin_two,
      Fin.sum_univ_two, Matrix.smul_apply] <;> ring

private lemma trace_eq_zero_of_sq_smul_one {M : Matrix (Fin 2) (Fin 2) (ZMod p)}
    (h01 : M 0 1 ≠ 0) {c : ZMod p} (h : M ^ 2 = c • 1) : M.trace = 0 := by
  by_contra ht
  have h2 : M.trace • M = (c + M.det) • 1 := by
    have h0 := (ch2 M).symm
    rw [h] at h0
    rw [sub_eq_iff_eq_add] at h0
    rwa [← add_smul] at h0
  have hM : M = ((M.trace)⁻¹ * (c + M.det)) • 1 := by
    rw [← smul_smul]
    exact (eq_inv_smul_iff₀ ht).mpr h2
  have h01' := congrFun (congrFun hM 0) 1
  simp [Matrix.smul_apply] at h01'
  exact h01 h01'

private lemma trace_sq_eq_det_of_cube_smul_one {M : Matrix (Fin 2) (Fin 2) (ZMod p)}
    (h01 : M 0 1 ≠ 0) {c : ZMod p} (h : M ^ 3 = c • 1) : M.trace ^ 2 = M.det := by
  by_contra ht
  have hne : M.trace ^ 2 - M.det ≠ 0 := sub_ne_zero.mpr ht
  have hkey : (M.trace ^ 2 - M.det) • M = (c + M.trace * M.det) • 1 := by
    have h0 := (mat_pow_three M).symm
    rw [h] at h0
    rw [sub_eq_iff_eq_add] at h0
    rwa [← add_smul] at h0
  have hM : M = ((M.trace ^ 2 - M.det)⁻¹ * (c + M.trace * M.det)) • 1 := by
    rw [← smul_smul]
    exact (eq_inv_smul_iff₀ hne).mpr hkey
  have h01' := congrFun (congrFun hM 0) 1
  simp [Matrix.smul_apply] at h01'
  exact h01 h01'

private lemma trace_eq_zero_or_trace_sq_eq_two_det_of_fourth
    {M : Matrix (Fin 2) (Fin 2) (ZMod p)}
    (h01 : M 0 1 ≠ 0) {c : ZMod p} (h : M ^ 4 = c • 1) :
    M.trace = 0 ∨ M.trace ^ 2 = 2 * M.det := by
  by_cases ht : M.trace = 0
  · exact Or.inl ht
  · right
    by_contra hd
    have hne : M.trace ^ 3 - 2 * M.trace * M.det ≠ 0 := by
      intro hc
      have hz : M.trace * (M.trace ^ 2 - 2 * M.det) = 0 := by rw [← hc]; ring
      rcases mul_eq_zero.mp hz with h | h
      · exact ht h
      · exact hd (sub_eq_zero.mp h)
    have hkey : (M.trace ^ 3 - 2 * M.trace * M.det) • M =
        (c - (M.det ^ 2 - M.trace ^ 2 * M.det)) • 1 := by
      have h0 := (mat_pow_four M).symm
      rw [h] at h0
      conv_rhs => rw [sub_smul]
      rw [eq_sub_iff_add_eq]
      exact h0
    have hM : M = ((M.trace ^ 3 - 2 * M.trace * M.det)⁻¹ *
        (c - (M.det ^ 2 - M.trace ^ 2 * M.det))) • 1 := by
      rw [← smul_smul]
      exact (eq_inv_smul_iff₀ hne).mpr hkey
    have h01' := congrFun (congrFun hM 0) 1
    simp [Matrix.smul_apply] at h01'
    exact h01 h01'

private lemma trace_fourth_eq_of_fifth {M : Matrix (Fin 2) (Fin 2) (ZMod p)}
    (h01 : M 0 1 ≠ 0) {c : ZMod p} (h : M ^ 5 = c • 1) :
    M.trace ^ 4 - 3 * M.trace ^ 2 * M.det + M.det ^ 2 = 0 := by
  by_contra ht
  have hne : M.trace ^ 4 - 3 * M.trace ^ 2 * M.det + M.det ^ 2 ≠ 0 := ht
  have hkey : (M.trace ^ 4 - 3 * M.trace ^ 2 * M.det + M.det ^ 2) • M =
      (c - (2 * M.trace * M.det ^ 2 - M.trace ^ 3 * M.det)) • 1 := by
    have h0 := (mat_pow_five M).symm
    rw [h] at h0
    conv_rhs => rw [sub_smul]
    rw [eq_sub_iff_add_eq]
    exact h0
  have hM : M = ((M.trace ^ 4 - 3 * M.trace ^ 2 * M.det + M.det ^ 2)⁻¹ *
      (c - (2 * M.trace * M.det ^ 2 - M.trace ^ 3 * M.det))) • 1 := by
    rw [← smul_smul]
    exact (eq_inv_smul_iff₀ hne).mpr hkey
  have h01' := congrFun (congrFun hM 0) 1
  simp [Matrix.smul_apply] at h01'
  exact h01 h01'

private lemma det_ne_zero_of_units (A : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
    Matrix.det ((A : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
      Matrix (Fin 2) (Fin 2) (ZMod p)) ≠ 0 := by
  intro h
  have h1 : ((A : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
        Matrix (Fin 2) (Fin 2) (ZMod p)) *
      (((A⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
        Matrix (Fin 2) (Fin 2) (ZMod p))) = 1 := Units.mul_inv A
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_mul, Matrix.det_one, h, zero_mul] at h2
  exact one_ne_zero h2.symm

private lemma pow_eq_one_of_sq (M : Matrix (Fin 2) (Fin 2) (ZMod p))
    (h : M ^ 2 = (2 : ZMod p) • M - 1) : M ^ p = 1 := by
  have h' : M * M = (2 : ZMod p) • M - 1 := by rw [← pow_two]; exact h
  have hN : (M - 1) ^ 2 = 0 := by
    rw [pow_two, sub_mul, mul_sub, one_mul, mul_one, h']
    module
  have hM : M = 1 + (M - 1) := by abel
  have key : ∀ n : ℕ, 2 ≤ n → (M - 1) ^ n = 0 := by
    intro n hn
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn
    rw [hk, pow_add, hN, zero_mul]
  calc M ^ p = (1 + (M - 1)) ^ p := by conv_lhs => rw [hM]
    _ = 1 ^ p + (M - 1) ^ p := add_pow_char_of_commute p (Commute.one_left (M - 1))
    _ = 1 := by
      rw [one_pow, key p (Fact.out : p.Prime).two_le, add_zero]

theorem mul_ne_sq_of_planePair {A B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)} {τ b b' : ZMod p}
    (hA : (A : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![τ, b; 0, 1])
    (hB : (B : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, 0; b', τ]) (hb : b ≠ 0)
    (hpf : ∀ g ∈ Subgroup.closure ({A, B} : Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))),
      g ^ p = 1 → g = 1) :
    b * b' ≠ (τ - 1) ^ 2 := by
  intro hq
  have hdetA : Matrix.det ((A : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
      Matrix (Fin 2) (Fin 2) (ZMod p)) = τ := by
    rw [hA, Matrix.det_fin_two_of]; ring
  have hτ0 : τ ≠ 0 := fun h => det_ne_zero_of_units A (by rw [hdetA, h])
  set m : Matrix (Fin 2) (Fin 2) (ZMod p) :=
    ((A * B⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
      Matrix (Fin 2) (Fin 2) (ZMod p)) with hm
  have hmul : m * (B : Matrix (Fin 2) (Fin 2) (ZMod p)) =
      (A : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
    rw [hm, ← Units.val_mul]
    congr 1
    group
  have e01 : m 0 1 * τ = b := by
    have h := congrFun (congrFun hmul 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two, hA, hB] using h
  have e11 : m 1 1 * τ = 1 := by
    have h := congrFun (congrFun hmul 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two, hA, hB] using h
  have e00 : m 0 0 + m 0 1 * b' = τ := by
    have h := congrFun (congrFun hmul 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two, hA, hB] using h
  have htr : m.trace = 2 := by
    have hτtr : τ * m.trace = τ * 2 := by
      rw [Matrix.trace_fin_two]
      linear_combination τ * e00 - b' * e01 + e11 - hq
    exact mul_left_cancel₀ hτ0 hτtr
  have hdet : m.det = 1 := by
    have h := congrArg Matrix.det hmul
    rw [Matrix.det_mul, hA, hB] at h
    simp [Matrix.det_fin_two_of] at h
    have h2 : m.det * τ = 1 * τ := by rw [h, one_mul]
    exact mul_right_cancel₀ hτ0 h2
  have hsq : m ^ 2 = (2 : ZMod p) • m - 1 := by
    rw [ch2, htr, hdet, one_smul]
  have hmp : m ^ p = 1 := pow_eq_one_of_sq m hsq
  have hGL : (A * B⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) ^ p = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, ← hm]
    exact hmp
  have hmem : A * B⁻¹ ∈ Subgroup.closure ({A, B} :
      Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))) :=
    Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp)))
  have hAB : A = B := mul_inv_eq_one.mp (hpf _ hmem hGL)
  have : b = 0 := by
    have h := congrArg (fun x : Matrix.GeneralLinearGroup (Fin 2) (ZMod p) =>
      (x : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1) hAB
    simpa [hA, hB] using h
  exact hb this

private lemma four_key {u : ZMod p} (h4 : (4 : ZMod p) ≠ 0) (h7 : (7 : ZMod p) ≠ 0)
    (hu : u ^ 2 = 0 ∨ u ^ 2 = 1 ∨ u ^ 2 = 2)
    (hv : (2 - u) ^ 2 = 0 ∨ (2 - u) ^ 2 = 1 ∨ (2 - u) ^ 2 = 2)
    (hu0 : u ≠ 0) (hu2 : u ≠ 2) : u = 1 := by
  rcases hu with h | h | h
  · exact absurd (sq_eq_zero_iff.mp h) hu0
  · rcases hv with h' | h' | h'
    · exact absurd (sub_eq_zero.mp (sq_eq_zero_iff.mp h')).symm hu2
    · have h4u : 4 * u = 4 := by linear_combination h - h'
      exact mul_left_cancel₀ h4 (by rw [h4u, mul_one])
    · have h4u : 4 * u = 3 := by linear_combination h - h'
      have h7eq : (7 : ZMod p) = 0 := by
        linear_combination (4 * u + 3) * h4u - 16 * h
      exact absurd h7eq h7
  · rcases hv with h' | h' | h'
    · exact absurd (sub_eq_zero.mp (sq_eq_zero_iff.mp h')).symm hu2
    · have h4u : 4 * u = 5 := by linear_combination h - h'
      have h7eq : (7 : ZMod p) = 0 := by
        linear_combination (4 * u + 5) * h4u - 16 * h
      exact absurd h7eq h7
    · have h4u : 4 * u = 4 := by linear_combination h - h'
      have hu1 : u = 1 := mul_left_cancel₀ h4 (by rw [h4u, mul_one])
      have h1eq : (1 : ZMod p) = 0 := by
        rw [hu1] at h
        linear_combination (-1) * h
      exact absurd h1eq one_ne_zero

theorem mul_eq_neg_of_planePair_four
    {A B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)} {τ b b' : ZMod p}
    (hA : (A : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![τ, b; 0, 1])
    (hB : (B : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, 0; b', τ]) (hb : b ≠ 0) (hb' : b' ≠ 0)
    (hpf : ∀ g ∈ Subgroup.closure ({A, B} : Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))),
      g ^ p = 1 → g = 1)
    (hτ : orderOf τ = 4) : b * b' = -τ := by
  have hdetA : Matrix.det ((A : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
      Matrix (Fin 2) (Fin 2) (ZMod p)) = τ := by
    rw [hA, Matrix.det_fin_two_of]; ring
  have hτ0 : τ ≠ 0 := fun h => det_ne_zero_of_units A (by rw [hdetA, h])
  have hτ4 : τ ^ 4 = 1 := by rw [← hτ]; exact pow_orderOf_eq_one τ
  have hτ2ne : τ ^ 2 ≠ 1 := by
    intro h
    have hd : orderOf τ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h
    rw [hτ] at hd
    omega
  have hτsq : τ ^ 2 = -1 := by
    have h : (τ ^ 2 - 1) * (τ ^ 2 + 1) = 0 := by
      rw [show (τ ^ 2 - 1) * (τ ^ 2 + 1) = τ ^ 4 - 1 by ring, hτ4, sub_self]
    rcases mul_eq_zero.mp h with h | h
    · exact absurd (sub_eq_zero.mp h) hτ2ne
    · exact eq_neg_of_add_eq_zero_left h
  have h4dvd : 4 ∣ p - 1 := by
    have hd := ZMod.orderOf_dvd_card_sub_one hτ0
    rwa [hτ] at hd
  have hp5 : 5 ≤ p := by
    obtain ⟨k, hk⟩ := h4dvd
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    omega
  have h4nz : (4 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 4 := (ZMod.natCast_eq_zero_iff 4 p).mp h
    exact Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega) hd
  have h7nz : (7 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 7 := (ZMod.natCast_eq_zero_iff 7 p).mp h
    have hp : p = 7 := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_seven).mp hd
    rw [hp] at h4dvd
    norm_num at h4dvd
  set u : ZMod p := (2 * τ + b * b') * τ⁻¹ with hudef
  have htu : τ * u = 2 * τ + b * b' := by
    rw [hudef]; field_simp
  have hmemP : A * B ∈ Subgroup.closure ({A, B} :
      Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))) :=
    Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  have hmemm : A * B⁻¹ ∈ Subgroup.closure ({A, B} :
      Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))) :=
    Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp)))
  set P : Matrix (Fin 2) (Fin 2) (ZMod p) :=
    (A : Matrix (Fin 2) (Fin 2) (ZMod p)) * (B : Matrix (Fin 2) (Fin 2) (ZMod p)) with hPdef
  have hPtrace : P.trace = τ * u := by
    have h1 : P.trace = 2 * τ + b * b' := by
      rw [hPdef, hA, hB]
      simp [Matrix.trace_fin_two]
      ring
    rw [h1, htu]
  have hPdet : P.det = τ ^ 2 := by
    rw [hPdef, Matrix.det_mul, hA, hB, Matrix.det_fin_two_of, Matrix.det_fin_two_of]
    ring
  have hP01 : P 0 1 ≠ 0 := by
    rw [hPdef, hA, hB]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    exact ⟨hb, hτ0⟩
  set m : Matrix (Fin 2) (Fin 2) (ZMod p) :=
    ((A * B⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
      Matrix (Fin 2) (Fin 2) (ZMod p)) with hmdef
  have hmul : m * (B : Matrix (Fin 2) (Fin 2) (ZMod p)) =
      (A : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
    rw [hmdef, ← Units.val_mul]
    congr 1
    group
  have e01 : m 0 1 * τ = b := by
    have h := congrFun (congrFun hmul 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two, hA, hB] using h
  have e11 : m 1 1 * τ = 1 := by
    have h := congrFun (congrFun hmul 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two, hA, hB] using h
  have e00 : m 0 0 + m 0 1 * b' = τ := by
    have h := congrFun (congrFun hmul 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two, hA, hB] using h
  have hm01 : m 0 1 ≠ 0 := fun h => hb (by rw [← e01, h, zero_mul])
  have hmtrace : m.trace = 2 - u := by
    have htu' : τ * (2 - u) = -(b * b') := by rw [mul_sub, htu]; ring
    have hτtr : τ * m.trace = τ * (2 - u) := by
      rw [htu', Matrix.trace_fin_two]
      linear_combination τ * e00 - b' * e01 + e11 + hτsq
    exact mul_left_cancel₀ hτ0 hτtr
  have hmdet : m.det = 1 := by
    have h := congrArg Matrix.det hmul
    rw [Matrix.det_mul, hA, hB] at h
    simp [Matrix.det_fin_two_of] at h
    have h2 : m.det * τ = 1 * τ := by rw [h, one_mul]
    exact mul_right_cancel₀ hτ0 h2
  have hu : u ^ 2 = 0 ∨ u ^ 2 = 1 ∨ u ^ 2 = 2 := by
    obtain ⟨c, hc | hc⟩ :=
      pow_eq_smul_of_planePair_four hA hB hb hb' hpf hτ (A * B) hmemP
    · have hP3 : P ^ 3 = c • 1 := by
        rw [hPdef, ← Units.val_mul, ← Units.val_pow_eq_pow_val]
        exact hc
      have hcnd := trace_sq_eq_det_of_cube_smul_one hP01 hP3
      have h1 : (τ * u) ^ 2 = τ ^ 2 := by rw [← hPtrace, ← hPdet]; exact hcnd
      have h2 : τ ^ 2 * u ^ 2 = τ ^ 2 := by conv_rhs => rw [← h1]; ring
      have hu1 : u ^ 2 = 1 :=
        mul_left_cancel₀ (pow_ne_zero 2 hτ0) (by rw [h2, mul_one])
      exact Or.inr (Or.inl hu1)
    · have hP4 : P ^ 4 = c • 1 := by
        rw [hPdef, ← Units.val_mul, ← Units.val_pow_eq_pow_val]
        exact hc
      have hcnd := trace_eq_zero_or_trace_sq_eq_two_det_of_fourth hP01 hP4
      rcases hcnd with h | h
      · have : u = 0 := by
          have h0 : τ * u = 0 := by rw [← hPtrace, h]
          exact (mul_eq_zero.mp h0).resolve_left hτ0
        exact Or.inl (by rw [this]; ring)
      · have h1 : (τ * u) ^ 2 = 2 * τ ^ 2 := by rw [← hPtrace, h, hPdet]
        have h2 : τ ^ 2 * u ^ 2 = 2 * τ ^ 2 := by
          conv_rhs => rw [← h1]
          ring
        have hu2 : u ^ 2 = 2 :=
          mul_left_cancel₀ (pow_ne_zero 2 hτ0) (by rw [h2, mul_comm])
        exact Or.inr (Or.inr hu2)
  have hv : (2 - u) ^ 2 = 0 ∨ (2 - u) ^ 2 = 1 ∨ (2 - u) ^ 2 = 2 := by
    obtain ⟨c, hc | hc⟩ :=
      pow_eq_smul_of_planePair_four hA hB hb hb' hpf hτ (A * B⁻¹) hmemm
    · have hm3 : m ^ 3 = c • 1 := by
        rw [hmdef, ← Units.val_pow_eq_pow_val]
        exact hc
      have hcnd := trace_sq_eq_det_of_cube_smul_one hm01 hm3
      have h1 : (2 - u) ^ 2 = 1 := by rw [← hmtrace, ← hmdet]; exact hcnd
      exact Or.inr (Or.inl h1)
    · have hm4 : m ^ 4 = c • 1 := by
        rw [hmdef, ← Units.val_pow_eq_pow_val]
        exact hc
      have hcnd := trace_eq_zero_or_trace_sq_eq_two_det_of_fourth hm01 hm4
      rcases hcnd with h | h
      · have h1 : (2 - u) ^ 2 = 0 := by rw [← hmtrace, h]; ring
        exact Or.inl h1
      · have h1 : (2 - u) ^ 2 = 2 := by
          rw [← hmtrace]
          rw [hmdet, mul_one] at h
          exact h
        exact Or.inr (Or.inr h1)
  have hu0 : u ≠ 0 := by
    intro h0
    have hbb : b * b' = -2 * τ := by
      have h : (2 * τ + b * b') = 0 := by
        have hh := congrArg (fun x : ZMod p => x * τ)
          (show (2 * τ + b * b') * τ⁻¹ = 0 from h0)
        rw [zero_mul] at hh
        rw [mul_assoc, inv_mul_cancel₀ hτ0, mul_one] at hh
        exact hh
      linear_combination h
    have hsq : (τ - 1) ^ 2 = -2 * τ := by linear_combination hτsq
    exact mul_ne_sq_of_planePair hA hB hb hpf (by rw [hbb, hsq])
  have hu2 : u ≠ 2 := by
    intro h0
    have hbb : b * b' = 0 := by
      have h : (2 * τ + b * b') = 2 * τ := by
        have hh := congrArg (fun x : ZMod p => x * τ)
          (show (2 * τ + b * b') * τ⁻¹ = 2 from h0)
        rw [mul_assoc, inv_mul_cancel₀ hτ0, mul_one] at hh
        exact hh
      linear_combination h
    exact hb ((mul_eq_zero.mp hbb).resolve_right hb')
  have hu1 : u = 1 := four_key h4nz h7nz hu hv hu0 hu2
  have h := htu
  rw [hu1, mul_one] at h
  linear_combination -h

private lemma zs19t_five_tau {τ : ZMod p} (hτ : orderOf τ = 5) :
    τ ≠ 0 ∧ τ ^ 5 = 1 ∧ τ ^ 4 + τ ^ 3 + τ ^ 2 + τ + 1 = 0 ∧ τ ≠ -1 ∧
      (2 : ZMod p) ≠ 0 ∧ (3 : ZMod p) ≠ 0 ∧ (5 : ZMod p) ≠ 0 := by
  have hτ0 : τ ≠ 0 := by
    intro h; rw [h] at hτ; simp at hτ
  have hτ5 : τ ^ 5 = 1 := by rw [← hτ]; exact pow_orderOf_eq_one τ
  have hτ1 : τ ≠ 1 := by
    intro h; rw [h] at hτ; simp at hτ
  have hΦ : τ ^ 4 + τ ^ 3 + τ ^ 2 + τ + 1 = 0 := by
    have h : (τ - 1) * (τ ^ 4 + τ ^ 3 + τ ^ 2 + τ + 1) = 0 := by
      linear_combination hτ5
    rcases mul_eq_zero.mp h with h | h
    · exact absurd (sub_eq_zero.mp h) hτ1
    · exact h
  have hτm1 : τ ≠ -1 := by
    intro h
    have h2 : τ ^ 2 = 1 := by rw [h]; ring
    have hd : orderOf τ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
    rw [hτ] at hd
    omega
  have h5dvd : 5 ∣ p - 1 := by
    have hd := ZMod.orderOf_dvd_card_sub_one hτ0
    rwa [hτ] at hd
  have h2nz : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    have hp : p = 2 := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hd
    rw [hp] at h5dvd; norm_num at h5dvd
  have h3nz : (3 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp h
    have hp : p = 3 := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).mp hd
    rw [hp] at h5dvd; norm_num at h5dvd
  have h5nz : (5 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 5 := (ZMod.natCast_eq_zero_iff 5 p).mp h
    have hp : p = 5 := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_five).mp hd
    rw [hp] at h5dvd; norm_num at h5dvd
  exact ⟨hτ0, hτ5, hΦ, hτm1, h2nz, h3nz, h5nz⟩

private lemma zs19t_five_K {τ : ZMod p} (hτ : orderOf τ = 5) :
    ∃ K : ZMod p, τ * K = (τ + 1) ^ 2 ∧ K ^ 2 = 3 * K - 1 ∧ K ≠ 0 := by
  obtain ⟨hτ0, hτ5, hΦ, hτm1, h2nz, h3nz, h5nz⟩ := zs19t_five_tau (p := p) hτ
  have htK : τ * (τ + 2 + τ⁻¹) = (τ + 1) ^ 2 := by field_simp; ring
  have hK : (τ + 2 + τ⁻¹) ^ 2 = 3 * (τ + 2 + τ⁻¹) - 1 := by
    have h : τ ^ 2 * ((τ + 2 + τ⁻¹) ^ 2 - 3 * (τ + 2 + τ⁻¹) + 1) = 0 := by
      linear_combination (τ * (τ + 2 + τ⁻¹) + (τ + 1) ^ 2 - 3 * τ) * htK + hΦ
    have hτ2nz : τ ^ 2 ≠ 0 := pow_ne_zero 2 hτ0
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hτ2nz
    · linear_combination h
  have hK0 : (τ + 2 + τ⁻¹) ≠ 0 := by
    intro h
    rw [h] at hK
    have h1 : (1 : ZMod p) = 0 := by linear_combination hK
    exact one_ne_zero h1
  exact ⟨τ + 2 + τ⁻¹, htK, hK, hK0⟩

private lemma zs19t_Ainv {A : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)} {τ b : ZMod p}
    (hA : (A : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![τ, b; 0, 1]) (hτ0 : τ ≠ 0) :
    ((A⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
      Matrix (Fin 2) (Fin 2) (ZMod p)) = !![τ⁻¹, -b * τ⁻¹; 0, 1] := by
  rw [Matrix.GeneralLinearGroup.coe_inv]
  apply Matrix.inv_eq_left_inv
  rw [hA]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals field_simp [hτ0]
  all_goals ring

private lemma zs19t_A2B {A B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)} {τ b b' : ZMod p}
    (hA : (A : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![τ, b; 0, 1])
    (hB : (B : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, 0; b', τ]) (hτ0 : τ ≠ 0) :
    ((A * A * B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
      Matrix (Fin 2) (Fin 2) (ZMod p)) =
      !![τ^2 + b * b' * (τ + 1), b * τ * (τ + 1); b', τ] := by
  rw [Units.val_mul, Units.val_mul, hA, hB]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals field_simp [hτ0]

private lemma zs19t_five_table {K u : ZMod p} (hK : K ^ 2 = 3 * K - 1) (hK0 : K ≠ 0)
    (h2nz : (2 : ZMod p) ≠ 0) (h3nz : (3 : ZMod p) ≠ 0) (h5nz : (5 : ZMod p) ≠ 0)
    (h1 : u ^ 2 = 0 ∨ u ^ 2 = 1 ∨ u ^ 2 = K ∨ u ^ 2 = 3 - K)
    (h2 : (K - u) ^ 2 = 0 ∨ (K - u) ^ 2 = 1 ∨ (K - u) ^ 2 = K ∨ (K - u) ^ 2 = 3 - K)
    (h3 : K * (u - 1) ^ 2 = 0 ∨ K * (u - 1) ^ 2 = 1 ∨ K * (u - 1) ^ 2 = K ∨
      K * (u - 1) ^ 2 = 3 - K) :
    u = 1 ∨ u = K - 1 := by
  rcases h1 with h1 | h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 | h2
  ·
    have hL : 2 * K * u = 3 * K - 1 := by linear_combination h1 - h2 + hK
    have h4 : 4 * K ^ 2 * (u - 1) ^ 2 = K := by
      linear_combination (2 * K * (u - 1) + (K - 1)) * hL + hK
    have h4v : 4 * (K * (u - 1) ^ 2) = 1 := by
      have h4' : K * (4 * (K * (u - 1) ^ 2)) = K * 1 := by linear_combination h4
      exact mul_left_cancel₀ hK0 h4'
    rcases h3 with h3 | h3 | h3 | h3
    · rw [h3] at h4v
      have : (1 : ZMod p) = 0 := by linear_combination -h4v
      exfalso; exact absurd this one_ne_zero
    · rw [h3] at h4v
      have : (3 : ZMod p) = 0 := by linear_combination h4v
      exfalso; exact h3nz this
    · rw [h3] at h4v
      have : (5 : ZMod p) = 0 := by linear_combination (11 - 4*K) * h4v + 16 * hK
      exfalso; exact h5nz this
    · rw [h3] at h4v
      have : (5 : ZMod p) = 0 := by linear_combination (4*K - 1) * h4v + 16 * hK
      exfalso; exact h5nz this
  ·
    have hN : (25 : ZMod p) = 0 := by
      linear_combination (-60*K^3 + 30*K^2*u + 205*K^2 - 80*K*u - 150*K + 80) * h1 +
        (-30*K^2*u - 45*K^2 + 80*K*u + 150*K - 80) * h2 +
        (30*K^2*u + 45*K^2 - 80*K*u - 15*K - 55) * hK
    have h5eq : (5 : ZMod p) = 0 := by
      have h : (5 : ZMod p) ^ 2 = 0 := by
        rw [show (5 : ZMod p) ^ 2 = (25 : ZMod p) by norm_num]; exact hN
      exact (pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0)).mp h
    exfalso; exact h5nz h5eq
  ·
    have hN : (1 : ZMod p) = 0 := by
      linear_combination (-32*K^3 + 16*K^2*u + 100*K^2 - 42*K*u - 50*K + 21) * h1 +
        (-16*K^2*u - 16*K^2 + 42*K*u + 50*K - 21) * h2 +
        (16*K^2*u + 16*K^2 - 42*K*u - 18*K + 1) * hK
    exfalso; exact absurd hN one_ne_zero
  ·
    have hN : (256 : ZMod p) = 0 := by
      linear_combination (-64*K^3 + 32*K^2*u + 256*K^2 - 96*K*u - 256*K + 192) * h1 +
        (-32*K^2*u - 64*K^2 + 96*K*u + 256*K - 192) * h2 +
        (32*K^2*u + 64*K^2 - 96*K*u - 320) * hK
    have h2eq : (2 : ZMod p) = 0 := by
      have h : (2 : ZMod p) ^ 8 = 0 := by
        rw [show (2 : ZMod p) ^ 8 = (256 : ZMod p) by norm_num]; exact hN
      exact (pow_eq_zero_iff (by norm_num : (8:ℕ) ≠ 0)).mp h
    exfalso; exact h2nz h2eq
  ·
    have hN : (25 : ZMod p) = 0 := by
      linear_combination (-60*K^3 + 30*K^2*u + 205*K^2 - 80*K*u - 120*K) * h1 +
        (-30*K^2*u - 45*K^2 + 80*K*u + 120*K) * h2 +
        (30*K^2*u + 45*K^2 - 80*K*u - 45*K + 25) * hK
    have h5eq : (5 : ZMod p) = 0 := by
      have h : (5 : ZMod p) ^ 2 = 0 := by
        rw [show (5 : ZMod p) ^ 2 = (25 : ZMod p) by norm_num]; exact hN
      exact (pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0)).mp h
    exfalso; exact h5nz h5eq
  ·
    have hL : 2 * K * u = 3 * K - 1 := by linear_combination h1 - h2 + hK
    have h4 : 4 * K ^ 2 * (u - 1) ^ 2 = K := by
      linear_combination (2 * K * (u - 1) + (K - 1)) * hL + hK
    have h4v : 4 * (K * (u - 1) ^ 2) = 1 := by
      have h4' : K * (4 * (K * (u - 1) ^ 2)) = K * 1 := by linear_combination h4
      exact mul_left_cancel₀ hK0 h4'
    rcases h3 with h3 | h3 | h3 | h3
    · rw [h3] at h4v
      have : (1 : ZMod p) = 0 := by linear_combination -h4v
      exfalso; exact absurd this one_ne_zero
    · rw [h3] at h4v
      have : (3 : ZMod p) = 0 := by linear_combination h4v
      exfalso; exact h3nz this
    · rw [h3] at h4v
      have : (5 : ZMod p) = 0 := by linear_combination (11 - 4*K) * h4v + 16 * hK
      exfalso; exact h5nz this
    · rw [h3] at h4v
      have : (5 : ZMod p) = 0 := by linear_combination (4*K - 1) * h4v + 16 * hK
      exfalso; exact h5nz this
  ·
    have hL : 2 * K * (u - 1) = 0 := by linear_combination h1 - h2 + hK
    have h2K : (2 : ZMod p) * K ≠ 0 := mul_ne_zero h2nz hK0
    have : u - 1 = 0 := (mul_eq_zero.mp hL).resolve_left h2K
    exact Or.inl (sub_eq_zero.mp this)
  ·
    have hN : (45 : ZMod p) = 0 := by
      linear_combination (-48*K^3 + 24*K^2*u + 180*K^2 - 66*K*u - 168*K + 99) * h1 +
        (-24*K^2*u - 48*K^2 + 66*K*u + 168*K - 99) * h2 +
        (24*K^2*u + 48*K^2 - 66*K*u - 24*K - 153) * hK
    have h : (3 : ZMod p) ^ 2 * 5 = 0 := by
      rw [show (3 : ZMod p) ^ 2 * 5 = (45 : ZMod p) by norm_num]; exact hN
    rcases mul_eq_zero.mp h with h | h
    · exfalso; exact h3nz ((pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0)).mp h)
    · exfalso; exact h5nz h
  ·
    have hN : (1 : ZMod p) = 0 := by
      linear_combination (-32*K^3 + 16*K^2*u + 116*K^2 - 42*K*u - 92*K + 21) * h1 +
        (-16*K^2*u - 32*K^2 + 42*K*u + 92*K - 21) * h2 +
        (16*K^2*u - 42*K*u + 24*K + 1) * hK
    exfalso; exact absurd hN one_ne_zero
  ·
    have hL : 2 * K * (u - (K - 1)) = 0 := by
      linear_combination h1 - h2 + hK - 2 * hK
    have h2K : (2 : ZMod p) * K ≠ 0 := mul_ne_zero h2nz hK0
    have : u - (K - 1) = 0 := (mul_eq_zero.mp hL).resolve_left h2K
    exact Or.inr (sub_eq_zero.mp this)
  ·
    have hL : 2 * K * u = 3 * K - 1 := by linear_combination h1 - h2 + hK
    have h4 : 4 * K ^ 2 * (u - 1) ^ 2 = K := by
      linear_combination (2 * K * (u - 1) + (K - 1)) * hL + hK
    have h4v : 4 * (K * (u - 1) ^ 2) = 1 := by
      have h4' : K * (4 * (K * (u - 1) ^ 2)) = K * 1 := by linear_combination h4
      exact mul_left_cancel₀ hK0 h4'
    rcases h3 with h3 | h3 | h3 | h3
    · rw [h3] at h4v
      have : (1 : ZMod p) = 0 := by linear_combination -h4v
      exfalso; exact absurd this one_ne_zero
    · rw [h3] at h4v
      have : (3 : ZMod p) = 0 := by linear_combination h4v
      exfalso; exact h3nz this
    · rw [h3] at h4v
      have : (5 : ZMod p) = 0 := by linear_combination (11 - 4*K) * h4v + 16 * hK
      exfalso; exact h5nz this
    · rw [h3] at h4v
      have : (5 : ZMod p) = 0 := by linear_combination (4*K - 1) * h4v + 16 * hK
      exfalso; exact h5nz this
  ·
    have hN : (45 : ZMod p) = 0 := by
      linear_combination (-12*K^3 + 6*K^2*u + 63*K^2 - 24*K*u - 72*K + 48) * h1 +
        (-6*K^2*u - 15*K^2 + 24*K*u + 72*K - 48) * h2 +
        (6*K^2*u + 3*K^2 - 24*K*u + 15*K - 99) * hK
    have h : (3 : ZMod p) ^ 2 * 5 = 0 := by
      rw [show (3 : ZMod p) ^ 2 * 5 = (45 : ZMod p) by norm_num]; exact hN
    rcases mul_eq_zero.mp h with h | h
    · exfalso; exact h3nz ((pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0)).mp h)
    · exfalso; exact h5nz h
  ·
    have hN : (256 : ZMod p) = 0 := by
      linear_combination (-64*K^3 + 32*K^2*u + 224*K^2 - 96*K*u - 64*K - 96) * h1 +
        (-32*K^2*u - 32*K^2 + 96*K*u + 64*K + 96) * h2 +
        (32*K^2*u + 96*K^2 - 96*K*u - 192*K - 32) * hK
    have h2eq : (2 : ZMod p) = 0 := by
      have h : (2 : ZMod p) ^ 8 = 0 := by
        rw [show (2 : ZMod p) ^ 8 = (256 : ZMod p) by norm_num]; exact hN
      exact (pow_eq_zero_iff (by norm_num : (8:ℕ) ≠ 0)).mp h
    exfalso; exact h2nz h2eq
  ·
    have hN : (45 : ZMod p) = 0 := by
      linear_combination (-48*K^3 + 24*K^2*u + 156*K^2 - 66*K*u - 54*K - 33) * h1 +
        (-24*K^2*u - 24*K^2 + 66*K*u + 54*K + 33) * h2 +
        (24*K^2*u + 72*K^2 - 66*K*u - 138*K - 21) * hK
    have h : (3 : ZMod p) ^ 2 * 5 = 0 := by
      rw [show (3 : ZMod p) ^ 2 * 5 = (45 : ZMod p) by norm_num]; exact hN
    rcases mul_eq_zero.mp h with h | h
    · exfalso; exact h3nz ((pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0)).mp h)
    · exfalso; exact h5nz h
  ·
    have hN : (45 : ZMod p) = 0 := by
      linear_combination (-12*K^3 + 6*K^2*u + 51*K^2 - 24*K*u - 6*K - 24) * h1 +
        (-6*K^2*u - 3*K^2 + 24*K*u + 6*K + 24) * h2 +
        (6*K^2*u + 15*K^2 - 24*K*u - 51*K - 27) * hK
    have h : (3 : ZMod p) ^ 2 * 5 = 0 := by
      rw [show (3 : ZMod p) ^ 2 * 5 = (45 : ZMod p) by norm_num]; exact hN
    rcases mul_eq_zero.mp h with h | h
    · exfalso; exact h3nz ((pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0)).mp h)
    · exfalso; exact h5nz h
  ·
    have hL : 2 * K * u = 3 * K - 1 := by linear_combination h1 - h2 + hK
    have h4 : 4 * K ^ 2 * (u - 1) ^ 2 = K := by
      linear_combination (2 * K * (u - 1) + (K - 1)) * hL + hK
    have h4v : 4 * (K * (u - 1) ^ 2) = 1 := by
      have h4' : K * (4 * (K * (u - 1) ^ 2)) = K * 1 := by linear_combination h4
      exact mul_left_cancel₀ hK0 h4'
    rcases h3 with h3 | h3 | h3 | h3
    · rw [h3] at h4v
      have : (1 : ZMod p) = 0 := by linear_combination -h4v
      exfalso; exact absurd this one_ne_zero
    · rw [h3] at h4v
      have : (3 : ZMod p) = 0 := by linear_combination h4v
      exfalso; exact h3nz this
    · rw [h3] at h4v
      have : (5 : ZMod p) = 0 := by linear_combination (11 - 4*K) * h4v + 16 * hK
      exfalso; exact h5nz this
    · rw [h3] at h4v
      have : (5 : ZMod p) = 0 := by linear_combination (4*K - 1) * h4v + 16 * hK
      exfalso; exact h5nz this

private lemma zs19t_AB_trace {A B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)} {τ b b' : ZMod p}
    (hA : (A : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![τ, b; 0, 1])
    (hB : (B : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, 0; b', τ]) :
    ((A * B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
      Matrix (Fin 2) (Fin 2) (ZMod p)).trace = 2 * τ + b * b' := by
  rw [Units.val_mul, hA, hB]
  simp [Matrix.trace_fin_two]
  ring

private lemma zs19t_AB_det {A B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)} {τ b b' : ZMod p}
    (hA : (A : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![τ, b; 0, 1])
    (hB : (B : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, 0; b', τ]) :
    ((A * B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
      Matrix (Fin 2) (Fin 2) (ZMod p)).det = τ ^ 2 := by
  rw [Units.val_mul, Matrix.det_mul, hA, hB, Matrix.det_fin_two_of, Matrix.det_fin_two_of]
  ring

private lemma zs19t_AB_01 {A B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)} {τ b b' : ZMod p}
    (hA : (A : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![τ, b; 0, 1])
    (hB : (B : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, 0; b', τ])
    (hb : b ≠ 0) (hτ0 : τ ≠ 0) :
    ((A * B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
      Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1 ≠ 0 := by
  rw [Units.val_mul, hA, hB]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  exact ⟨hb, hτ0⟩

private lemma zs19t_AinvB_trace {A B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)}
    {τ b b' : ZMod p}
    (hA : (A : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![τ, b; 0, 1])
    (hB : (B : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, 0; b', τ]) (hτ0 : τ ≠ 0) :
    ((A⁻¹ * B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
      Matrix (Fin 2) (Fin 2) (ZMod p)).trace = τ⁻¹ * (1 - b * b') + τ := by
  rw [Units.val_mul, zs19t_Ainv hA hτ0, hB]
  simp [Matrix.trace_fin_two]
  ring

private lemma zs19t_AinvB_det {A B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)}
    {τ b b' : ZMod p}
    (hA : (A : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![τ, b; 0, 1])
    (hB : (B : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, 0; b', τ]) (hτ0 : τ ≠ 0) :
    ((A⁻¹ * B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
      Matrix (Fin 2) (Fin 2) (ZMod p)).det = 1 := by
  rw [Units.val_mul, zs19t_Ainv hA hτ0, hB, Matrix.det_mul, Matrix.det_fin_two_of,
    Matrix.det_fin_two_of]
  field_simp [hτ0]
  ring

private lemma zs19t_AinvB_01 {A B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)}
    {τ b b' : ZMod p}
    (hA : (A : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![τ, b; 0, 1])
    (hB : (B : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, 0; b', τ]) (hτ0 : τ ≠ 0)
    (hb : b ≠ 0) :
    ((A⁻¹ * B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
      Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1 ≠ 0 := by
  rw [Units.val_mul, zs19t_Ainv hA hτ0, hB]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  exact ⟨hb, hτ0⟩

private lemma zs19t_A2B_trace {A B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)}
    {τ b b' : ZMod p}
    (hA : (A : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![τ, b; 0, 1])
    (hB : (B : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, 0; b', τ]) :
    ((A * A * B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
      Matrix (Fin 2) (Fin 2) (ZMod p)).trace = (τ + 1) * (τ + b * b') := by
  rw [Units.val_mul, Units.val_mul, hA, hB]
  simp [Matrix.trace_fin_two]
  ring_nf

private lemma zs19t_A2B_det {A B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)}
    {τ b b' : ZMod p}
    (hA : (A : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![τ, b; 0, 1])
    (hB : (B : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, 0; b', τ]) :
    ((A * A * B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
      Matrix (Fin 2) (Fin 2) (ZMod p)).det = τ ^ 3 := by
  rw [Units.val_mul, Units.val_mul, hA, hB, Matrix.det_mul, Matrix.det_mul]
  simp [Matrix.det_fin_two_of]
  ring_nf

private lemma zs19t_A2B_01 {A B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)}
    {τ b b' : ZMod p}
    (hA : (A : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![τ, b; 0, 1])
    (hB : (B : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, 0; b', τ])
    (hτ0 : τ ≠ 0) (hτm1 : τ ≠ -1) (hb : b ≠ 0) :
    ((A * A * B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
      Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1 ≠ 0 := by
  rw [zs19t_A2B hA hB hτ0]
  simp
  exact ⟨⟨hb, hτ0⟩, by intro h; exact hτm1 (by linear_combination h)⟩

private lemma zs19t_five_h1 {A B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)}
    {τ b b' : ZMod p} (hA : (A : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![τ, b; 0, 1])
    (hB : (B : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, 0; b', τ]) (hb : b ≠ 0) (hb' : b' ≠ 0)
    (hpf : ∀ g ∈ Subgroup.closure ({A, B} : Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))),
      g ^ p = 1 → g = 1)
    (hτ : orderOf τ = 5) {K u : ZMod p} (htu : τ * u = 2 * τ + b * b') (hK : K ^ 2 = 3 * K - 1) :
    u ^ 2 = 0 ∨ u ^ 2 = 1 ∨ u ^ 2 = K ∨ u ^ 2 = 3 - K := by
  obtain ⟨hτ0, hτ5, hΦ, hτm1, h2nz, h3nz, h5nz⟩ := zs19t_five_tau (p := p) hτ
  have hmem : A * B ∈ Subgroup.closure ({A, B} :
      Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))) :=
    Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  have h01 : (((A * B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
      Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1) ≠ 0 := zs19t_AB_01 hA hB hb hτ0
  obtain ⟨c, hc | hc | hc⟩ :=
    pow_eq_smul_of_planePair_five hA hB hb hb' hpf hτ (A * B) hmem
  · have hM : (((A * B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
        Matrix (Fin 2) (Fin 2) (ZMod p))) ^ 2 = c • 1 := by
      rw [← Units.val_pow_eq_pow_val]; exact hc
    have ht := trace_eq_zero_of_sq_smul_one h01 hM
    left
    have h0 : τ * u = 0 := by
      rw [htu, ← zs19t_AB_trace hA hB]; exact ht
    have hu0 : u = 0 := (mul_eq_zero.mp h0).resolve_left hτ0
    rw [hu0]; ring
  · have hM : (((A * B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
        Matrix (Fin 2) (Fin 2) (ZMod p))) ^ 3 = c • 1 := by
      rw [← Units.val_pow_eq_pow_val]; exact hc
    have ht := trace_sq_eq_det_of_cube_smul_one h01 hM
    right; left
    have h1' : (τ * u) ^ 2 = τ ^ 2 := by
      rw [htu, ← zs19t_AB_trace hA hB, ← zs19t_AB_det hA hB]; exact ht
    have hu2 : u ^ 2 = 1 := by
      have h2' : τ ^ 2 * u ^ 2 = τ ^ 2 := by conv_rhs => rw [← h1']; ring
      exact mul_left_cancel₀ (pow_ne_zero 2 hτ0) (by rw [h2', mul_one])
    exact hu2
  · have hM : (((A * B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
        Matrix (Fin 2) (Fin 2) (ZMod p))) ^ 5 = c • 1 := by
      rw [← Units.val_pow_eq_pow_val]; exact hc
    have ht := trace_fourth_eq_of_fifth h01 hM
    right; right
    have hu4 : u ^ 4 - 3 * u ^ 2 + 1 = 0 := by
      have h : (τ * u) ^ 4 - 3 * (τ * u) ^ 2 * τ ^ 2 + (τ ^ 2) ^ 2 = 0 := by
        rw [htu, ← zs19t_AB_trace hA hB, ← zs19t_AB_det hA hB]; exact ht
      have h2 : τ ^ 4 * (u ^ 4 - 3 * u ^ 2 + 1) = 0 := by linear_combination h
      exact (mul_eq_zero.mp h2).resolve_left (pow_ne_zero 4 hτ0)
    have hfac : (u ^ 2 - K) * (u ^ 2 - (3 - K)) = 0 := by linear_combination hu4 - hK
    rcases mul_eq_zero.mp hfac with h | h
    · left; linear_combination h
    · right; linear_combination h

private lemma zs19t_five_h2 {A B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)}
    {τ b b' : ZMod p} (hA : (A : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![τ, b; 0, 1])
    (hB : (B : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, 0; b', τ]) (hb : b ≠ 0) (hb' : b' ≠ 0)
    (hpf : ∀ g ∈ Subgroup.closure ({A, B} : Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))),
      g ^ p = 1 → g = 1)
    (hτ : orderOf τ = 5) {K u : ZMod p} (htK : τ * K = (τ + 1) ^ 2)
    (htu : τ * u = 2 * τ + b * b') (hτ0 : τ ≠ 0) (hK : K ^ 2 = 3 * K - 1) :
    (K - u) ^ 2 = 0 ∨ (K - u) ^ 2 = 1 ∨ (K - u) ^ 2 = K ∨ (K - u) ^ 2 = 3 - K := by
  have hmem : A⁻¹ * B ∈ Subgroup.closure ({A, B} :
      Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp)))
      (Subgroup.subset_closure (by simp))
  have h01 : (((A⁻¹ * B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
      Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1) ≠ 0 := zs19t_AinvB_01 hA hB hτ0 hb
  have hMtr : (((A⁻¹ * B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
      Matrix (Fin 2) (Fin 2) (ZMod p))).trace = K - u := by
    rw [zs19t_AinvB_trace hA hB hτ0]
    apply mul_left_cancel₀ hτ0
    rw [mul_add, ← mul_assoc, mul_inv_cancel₀ hτ0, one_mul]
    rw [mul_sub, htK, htu]
    ring
  have hMdet : (((A⁻¹ * B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
      Matrix (Fin 2) (Fin 2) (ZMod p))).det = 1 := zs19t_AinvB_det hA hB hτ0
  obtain ⟨c, hc | hc | hc⟩ :=
    pow_eq_smul_of_planePair_five hA hB hb hb' hpf hτ (A⁻¹ * B) hmem
  · have hM : (((A⁻¹ * B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
        Matrix (Fin 2) (Fin 2) (ZMod p))) ^ 2 = c • 1 := by
      rw [← Units.val_pow_eq_pow_val]; exact hc
    have ht := trace_eq_zero_of_sq_smul_one h01 hM
    left
    have h0 : K - u = 0 := by rw [← hMtr]; exact ht
    rw [h0]; ring
  · have hM : (((A⁻¹ * B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
        Matrix (Fin 2) (Fin 2) (ZMod p))) ^ 3 = c • 1 := by
      rw [← Units.val_pow_eq_pow_val]; exact hc
    have ht := trace_sq_eq_det_of_cube_smul_one h01 hM
    right; left
    rw [hMtr, hMdet] at ht
    exact ht
  · have hM : (((A⁻¹ * B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
        Matrix (Fin 2) (Fin 2) (ZMod p))) ^ 5 = c • 1 := by
      rw [← Units.val_pow_eq_pow_val]; exact hc
    have ht := trace_fourth_eq_of_fifth h01 hM
    right; right
    have h4 : (K - u) ^ 4 - 3 * (K - u) ^ 2 + 1 = 0 := by
      rw [hMtr, hMdet] at ht
      linear_combination ht
    have hfac : ((K - u) ^ 2 - K) * ((K - u) ^ 2 - (3 - K)) = 0 := by
      linear_combination h4 - hK
    rcases mul_eq_zero.mp hfac with h | h
    · left; linear_combination h
    · right; linear_combination h

private lemma zs19t_five_h3 {A B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)}
    {τ b b' : ZMod p} (hA : (A : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![τ, b; 0, 1])
    (hB : (B : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, 0; b', τ]) (hb : b ≠ 0) (hb' : b' ≠ 0)
    (hpf : ∀ g ∈ Subgroup.closure ({A, B} : Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))),
      g ^ p = 1 → g = 1)
    (hτ : orderOf τ = 5) {K u : ZMod p} (htK : τ * K = (τ + 1) ^ 2)
    (htu : τ * u = 2 * τ + b * b') (hτ0 : τ ≠ 0) (hτm1 : τ ≠ -1)
    (hK : K ^ 2 = 3 * K - 1) :
    K * (u - 1) ^ 2 = 0 ∨ K * (u - 1) ^ 2 = 1 ∨ K * (u - 1) ^ 2 = K ∨
      K * (u - 1) ^ 2 = 3 - K := by
  have hmem : A * A * B ∈ Subgroup.closure ({A, B} :
      Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))) (Subgroup.subset_closure (by simp))
  have h01 : (((A * A * B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
      Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1) ≠ 0 := zs19t_A2B_01 hA hB hτ0 hτm1 hb
  have htu' : τ * (u - 1) = τ + b * b' := by linear_combination htu
  have hMtr : (((A * A * B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
      Matrix (Fin 2) (Fin 2) (ZMod p))).trace = τ * (τ + 1) * (u - 1) := by
    rw [zs19t_A2B_trace hA hB]
    linear_combination (-(τ + 1)) * htu'
  have hMdet : (((A * A * B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
      Matrix (Fin 2) (Fin 2) (ZMod p))).det = τ ^ 3 := zs19t_A2B_det hA hB
  obtain ⟨c, hc | hc | hc⟩ :=
    pow_eq_smul_of_planePair_five hA hB hb hb' hpf hτ (A * A * B) hmem
  · have hM : (((A * A * B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
        Matrix (Fin 2) (Fin 2) (ZMod p))) ^ 2 = c • 1 := by
      rw [← Units.val_pow_eq_pow_val]; exact hc
    have ht := trace_eq_zero_of_sq_smul_one h01 hM
    have h0 : u = 1 := by
      have h1 : τ * (τ + 1) * (u - 1) = 0 := by rw [← hMtr]; exact ht
      rcases mul_eq_zero.mp h1 with h1 | h1
      · rcases mul_eq_zero.mp h1 with h1 | h1
        · exact absurd h1 hτ0
        · exact absurd (by linear_combination h1 : τ = -1) hτm1
      · exact sub_eq_zero.mp h1
    left
    rw [h0]; ring
  · have hM : (((A * A * B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
        Matrix (Fin 2) (Fin 2) (ZMod p))) ^ 3 = c • 1 := by
      rw [← Units.val_pow_eq_pow_val]; exact hc
    have ht := trace_sq_eq_det_of_cube_smul_one h01 hM
    right; left
    have h := ht
    rw [hMtr, hMdet] at h
    have h2 : (τ + 1) ^ 2 * (u - 1) ^ 2 = τ := by
      have h' : τ ^ 2 * ((τ + 1) ^ 2 * (u - 1) ^ 2) = τ ^ 2 * τ := by linear_combination h
      exact mul_left_cancel₀ (pow_ne_zero 2 hτ0) h'
    have h3 : τ * (K * (u - 1) ^ 2) = τ * 1 := by
      rw [← mul_assoc, htK]; linear_combination h2
    exact mul_left_cancel₀ hτ0 h3
  · have hM : (((A * A * B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
        Matrix (Fin 2) (Fin 2) (ZMod p))) ^ 5 = c • 1 := by
      rw [← Units.val_pow_eq_pow_val]; exact hc
    have ht := trace_fourth_eq_of_fifth h01 hM
    right; right
    have h := ht
    rw [hMtr, hMdet] at h
    have h4 : (K * (u - 1) ^ 2) ^ 2 - 3 * (K * (u - 1) ^ 2) + 1 = 0 := by
      have h' : τ ^ 6 * ((K * (u - 1) ^ 2) ^ 2 - 3 * (K * (u - 1) ^ 2) + 1) = 0 := by
        linear_combination h +
          (τ ^ 4 * (u - 1) ^ 4 * (τ * K + (τ + 1) ^ 2) - 3 * τ ^ 5 * (u - 1) ^ 2) * htK
      exact (mul_eq_zero.mp h').resolve_left (pow_ne_zero 6 hτ0)
    have hfac : (K * (u - 1) ^ 2 - K) * (K * (u - 1) ^ 2 - (3 - K)) = 0 := by
      linear_combination h4 - hK
    rcases mul_eq_zero.mp hfac with h | h
    · left; linear_combination h
    · right; linear_combination h

theorem mul_eq_of_planePair_five
    {A B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)} {τ b b' : ZMod p}
    (hA : (A : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![τ, b; 0, 1])
    (hB : (B : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, 0; b', τ]) (hb : b ≠ 0) (hb' : b' ≠ 0)
    (hpf : ∀ g ∈ Subgroup.closure ({A, B} : Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))),
      g ^ p = 1 → g = 1)
    (hτ : orderOf τ = 5) : b * b' = -τ ∨ b * b' = τ ^ 2 - τ + 1 := by
  obtain ⟨hτ0, hτ5, hΦ, hτm1, h2nz, h3nz, h5nz⟩ := zs19t_five_tau (p := p) hτ
  obtain ⟨K, htK, hK, hK0⟩ := zs19t_five_K (p := p) hτ
  set u : ZMod p := (2 * τ + b * b') * τ⁻¹ with hudef
  have htu : τ * u = 2 * τ + b * b' := by rw [hudef]; field_simp
  have h1 := zs19t_five_h1 hA hB hb hb' hpf hτ htu hK
  have h2 := zs19t_five_h2 hA hB hb hb' hpf hτ htK htu hτ0 hK
  have h3 := zs19t_five_h3 hA hB hb hb' hpf hτ htK htu hτ0 hτm1 hK
  have huv := zs19t_five_table hK hK0 h2nz h3nz h5nz h1 h2 h3
  rcases huv with hu | hu
  · left
    have h := htu
    rw [hu, mul_one] at h
    linear_combination -h
  · right
    have h := htu
    rw [hu] at h
    linear_combination -h + htK

private lemma zs19t_conj_final (p : ℕ) {A k : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)}
    {τ : ZMod p}
    (hk : (A : Matrix (Fin 2) (Fin 2) (ZMod p)) *
      (k : Matrix (Fin 2) (Fin 2) (ZMod p)) *
      (A : Matrix (Fin 2) (Fin 2) (ZMod p)) = τ • (k : Matrix (Fin 2) (Fin 2) (ZMod p))) :
    ((k * A * k⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
      Matrix (Fin 2) (Fin 2) (ZMod p)) =
      τ • ((A⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
        Matrix (Fin 2) (Fin 2) (ZMod p)) := by
  rw [Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_inv,
    Matrix.GeneralLinearGroup.coe_inv]
  have hA : ((A⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
      Matrix (Fin 2) (Fin 2) (ZMod p)) * (A : Matrix (Fin 2) (Fin 2) (ZMod p)) = 1 :=
    Units.inv_mul A
  have hk1 : (k : Matrix (Fin 2) (Fin 2) (ZMod p)) *
      ((k⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
        Matrix (Fin 2) (Fin 2) (ZMod p)) = 1 :=
    Units.mul_inv k
  have h2 : ((A⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
        Matrix (Fin 2) (Fin 2) (ZMod p)) *
      ((A : Matrix (Fin 2) (Fin 2) (ZMod p)) *
        (k : Matrix (Fin 2) (Fin 2) (ZMod p)) *
        (A : Matrix (Fin 2) (Fin 2) (ZMod p))) =
      (k : Matrix (Fin 2) (Fin 2) (ZMod p)) * (A : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
    rw [← mul_assoc ((A⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
          Matrix (Fin 2) (Fin 2) (ZMod p)) ((A : Matrix (Fin 2) (Fin 2) (ZMod p)) *
          (k : Matrix (Fin 2) (Fin 2) (ZMod p))) (A : Matrix (Fin 2) (Fin 2) (ZMod p)),
        ← mul_assoc ((A⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
          Matrix (Fin 2) (Fin 2) (ZMod p)) (A : Matrix (Fin 2) (Fin 2) (ZMod p))
          (k : Matrix (Fin 2) (Fin 2) (ZMod p)), hA, one_mul]
  rw [show (k : Matrix (Fin 2) (Fin 2) (ZMod p)) * (A : Matrix (Fin 2) (Fin 2) (ZMod p)) =
      ((A⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
        Matrix (Fin 2) (Fin 2) (ZMod p)) *
      ((A : Matrix (Fin 2) (Fin 2) (ZMod p)) * (k : Matrix (Fin 2) (Fin 2) (ZMod p)) *
        (A : Matrix (Fin 2) (Fin 2) (ZMod p))) from h2.symm]
  rw [hk, Matrix.mul_smul, Matrix.smul_mul, mul_assoc, ← Matrix.GeneralLinearGroup.coe_inv k, hk1,
    mul_one, Matrix.GeneralLinearGroup.coe_inv]

private lemma zs19t_conj_four_matrix (p : ℕ) {A B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)}
    {τ b b' : ZMod p}
    (hA : (A : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![τ, b; 0, 1])
    (hB : (B : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, 0; b', τ])
    (hq : b * b' = -τ) (hΦ : τ^2 + 1 = 0) :
    (A : Matrix (Fin 2) (Fin 2) (ZMod p)) *
      (((B*B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p))) *
      (A : Matrix (Fin 2) (Fin 2) (ZMod p)) =
      τ • (((B*B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
        Matrix (Fin 2) (Fin 2) (ZMod p))) := by
  rw [Units.val_mul, hA, hB]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]
  · linear_combination (τ+τ^2) * hq - τ * hΦ
  · linear_combination (τ*b+b) * hq
  · ring
  · linear_combination (τ+1) * hq - τ * hΦ

private lemma zs19t_conj_five_pos_matrix (p : ℕ) {A B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)}
    {τ b b' : ZMod p}
    (hA : (A : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![τ, b; 0, 1])
    (hB : (B : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, 0; b', τ])
    (hq : b * b' = τ^2 - τ + 1) (hΦ : τ^4 + τ^3 + τ^2 + τ + 1 = 0) :
    (A : Matrix (Fin 2) (Fin 2) (ZMod p)) *
      (((B*A*B*B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p))) *
      (A : Matrix (Fin 2) (Fin 2) (ZMod p)) =
      τ • (((B*A*B*B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
        Matrix (Fin 2) (Fin 2) (ZMod p))) := by
  rw [Units.val_mul, Units.val_mul, Units.val_mul, hA, hB]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]
  · linear_combination (τ^4 + 2*τ^3 + τ^2*b*b' + 2*τ^2 + τ*b*b') * hq + (τ^2) * hΦ
  · linear_combination (τ^3*b + 3*τ^2*b + τ*b^2*b' + 3*τ*b + b^2*b' + b) * hq + (τ*b + b) * hΦ
  · ring
  · linear_combination (2*τ^2 + τ*b*b' + 2*τ + b*b' + 1) * hq + (1) * hΦ

private lemma zs19t_conj_five_neg_matrix (p : ℕ) {A B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)}
    {τ b b' : ZMod p}
    (hA : (A : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![τ, b; 0, 1])
    (hB : (B : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, 0; b', τ])
    (hq : b * b' = -τ) (hΦ : τ^4 + τ^3 + τ^2 + τ + 1 = 0) :
    (A : Matrix (Fin 2) (Fin 2) (ZMod p)) *
      (((B*A*A*A*A*B*B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
        Matrix (Fin 2) (Fin 2) (ZMod p))) *
      (A : Matrix (Fin 2) (Fin 2) (ZMod p)) =
      τ • (((B*A*A*A*A*B*B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
        Matrix (Fin 2) (Fin 2) (ZMod p))) := by
  rw [Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul,
    Units.val_mul, hA, hB]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]
  · linear_combination (τ^5*b*b' + 2*τ^4*b*b' - 2*τ^4 + 2*τ^3*b*b' - τ^3 +
      2*τ^2*b*b' - τ^2 + τ*b*b' - τ) * hq + (τ^2) * hΦ
  · linear_combination (τ^5*b + τ^4*b^2*b' + 2*τ^4*b + 2*τ^3*b^2*b' + τ^3*b +
      2*τ^2*b^2*b' + 2*τ^2*b + 2*τ*b^2*b' + τ*b + b^2*b') * hq + (-τ^2*b) * hΦ
  · ring
  · linear_combination (-τ^6 - τ^5 + τ^4*b*b' - τ^4 + 2*τ^3*b*b' - 2*τ^3 +
      2*τ^2*b*b' + 2*τ*b*b' + b*b') * hq + (τ^3) * hΦ

theorem exists_conj_eq_smul_inv_of_planePair
    {A B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)} {τ b b' : ZMod p}
    (hA : (A : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![τ, b; 0, 1])
    (hB : (B : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, 0; b', τ]) (hb : b ≠ 0) (hb' : b' ≠ 0)
    (hpf : ∀ g ∈ Subgroup.closure ({A, B} : Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))),
      g ^ p = 1 → g = 1)
    (hτ : 4 ≤ orderOf τ) :
    ∃ k ∈ Subgroup.closure ({A, B} : Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))),
      ((k * A * k⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
        Matrix (Fin 2) (Fin 2) (ZMod p)) =
        τ • ((A⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
          Matrix (Fin 2) (Fin 2) (ZMod p)) := by
  have hA_mem : A ∈ Subgroup.closure ({A, B} : Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))) :=
    Subgroup.subset_closure (by simp)
  have hB_mem : B ∈ Subgroup.closure ({A, B} : Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))) :=
    Subgroup.subset_closure (by simp)
  have hm := orderOf_eq_four_or_five_of_planePair hA hB hb hb' hpf hτ
  rcases hm with hτ4 | hτ5
  · have hq := mul_eq_neg_of_planePair_four hA hB hb hb' hpf hτ4
    have hτ4' : τ ^ 4 = 1 := by rw [← hτ4]; exact pow_orderOf_eq_one τ
    have hτ2ne : τ ^ 2 ≠ 1 := by
      intro h
      have hd : orderOf τ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h
      rw [hτ4] at hd
      omega
    have hΦ : τ ^ 2 + 1 = 0 := by
      have h : (τ ^ 2 - 1) * (τ ^ 2 + 1) = 0 := by
        rw [show (τ ^ 2 - 1) * (τ ^ 2 + 1) = τ ^ 4 - 1 by ring, hτ4', sub_self]
      rcases mul_eq_zero.mp h with h | h
      · exact absurd (sub_eq_zero.mp h) hτ2ne
      · exact h
    have hk := zs19t_conj_four_matrix p hA hB hq hΦ
    refine ⟨B * B, ?_, ?_⟩
    · exact Subgroup.mul_mem _ hB_mem hB_mem
    · exact zs19t_conj_final p hk
  · have hq := mul_eq_of_planePair_five hA hB hb hb' hpf hτ5
    have hτ5' : τ ^ 5 = 1 := by rw [← hτ5]; exact pow_orderOf_eq_one τ
    have hτ1 : τ ≠ 1 := by intro h; rw [h] at hτ5; simp at hτ5
    have hΦ : τ ^ 4 + τ ^ 3 + τ ^ 2 + τ + 1 = 0 := by
      have h : (τ - 1) * (τ ^ 4 + τ ^ 3 + τ ^ 2 + τ + 1) = 0 := by
        linear_combination hτ5'
      rcases mul_eq_zero.mp h with h | h
      · exact absurd (sub_eq_zero.mp h) hτ1
      · exact h
    rcases hq with hq | hq
    · have hk := zs19t_conj_five_neg_matrix p hA hB hq hΦ
      refine ⟨B * A * A * A * A * B * B, ?_, ?_⟩
      · have h1 : B * A ∈ Subgroup.closure ({A, B} :
            Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))) := Subgroup.mul_mem _ hB_mem hA_mem
        have h2 : B * A * A ∈ Subgroup.closure ({A, B} :
            Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))) := Subgroup.mul_mem _ h1 hA_mem
        have h3 : B * A * A * A ∈ Subgroup.closure ({A, B} :
            Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))) := Subgroup.mul_mem _ h2 hA_mem
        have h4 : B * A * A * A * A ∈ Subgroup.closure ({A, B} :
            Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))) := Subgroup.mul_mem _ h3 hA_mem
        have h5 : B * A * A * A * A * B ∈ Subgroup.closure ({A, B} :
            Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))) := Subgroup.mul_mem _ h4 hB_mem
        exact Subgroup.mul_mem _ h5 hB_mem
      · exact zs19t_conj_final p hk
    · have hk := zs19t_conj_five_pos_matrix p hA hB hq hΦ
      refine ⟨B * A * B * B, ?_, ?_⟩
      · have h1 : B * A ∈ Subgroup.closure ({A, B} :
            Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))) := Subgroup.mul_mem _ hB_mem hA_mem
        have h2 : B * A * B ∈ Subgroup.closure ({A, B} :
            Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))) := Subgroup.mul_mem _ h1 hB_mem
        exact Subgroup.mul_mem _ h2 hB_mem
      · exact zs19t_conj_final p hk

end CFSG.StandardType.ZS

end
