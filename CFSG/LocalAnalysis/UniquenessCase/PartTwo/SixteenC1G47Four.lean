module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

namespace S16C1G47Four

open Polynomial Matrix

private theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

private theorem selfRecip_dvd {p : (ZMod 2)[X]} (hm : p.Monic) (hd : p.natDegree ≤ 4)
    (hr : p.reverse = p) : ∃ k, 1 ≤ k ∧ k ≤ 6 ∧ p ∣ X ^ k - 1 := by
  have hc : ∀ i ≤ p.natDegree, p.coeff i = p.coeff (p.natDegree - i) := by
    intro i hi
    have h := congrArg (fun q => q.coeff i) hr
    simpa [Polynomial.coeff_reverse, Polynomial.revAt_le hi] using h.symm
  have hlead : p.coeff p.natDegree = 1 := hm.coeff_natDegree
  have hsum := hm.as_sum
  obtain ⟨n, hn⟩ : ∃ n, p.natDegree = n := ⟨_, rfl⟩
  rw [hn] at hc hlead hsum hd
  interval_cases n
  · simp at hsum
    exact ⟨1, le_rfl, by norm_num, by rw [hsum]; exact one_dvd _⟩
  · have h0 : p.coeff 0 = 1 := by
      have := hc 0 (by norm_num)
      simpa [hlead] using this
    simp [Finset.sum_range_succ, h0] at hsum
    refine ⟨1, le_rfl, by norm_num, ?_⟩
    rw [hsum]
    exact ⟨1, by rw [CharTwo.sub_eq_add]; ring⟩
  · have h0 : p.coeff 0 = 1 := by
      have := hc 0 (by norm_num)
      simpa [hlead] using this
    rcases zmod2_cases (p.coeff 1) with h1 | h1
    · simp [Finset.sum_range_succ, h0, h1] at hsum
      refine ⟨2, by norm_num, by norm_num, ?_⟩
      rw [hsum]
      exact ⟨1, by rw [CharTwo.sub_eq_add]; ring_nf⟩
    · simp [Finset.sum_range_succ, h0, h1] at hsum
      refine ⟨3, by norm_num, by norm_num, ?_⟩
      rw [hsum]
      exact ⟨X + 1, by rw [CharTwo.sub_eq_add]; ring_nf; try reduce_mod_char⟩
  · have h0 : p.coeff 0 = 1 := by
      have := hc 0 (by norm_num)
      simpa [hlead] using this
    have h12 : p.coeff 1 = p.coeff 2 := hc 1 (by norm_num)
    rcases zmod2_cases (p.coeff 1) with h1 | h1
    · have h2 : p.coeff 2 = 0 := h12 ▸ h1
      simp [Finset.sum_range_succ, h0, h1, h2] at hsum
      refine ⟨3, by norm_num, by norm_num, ?_⟩
      rw [hsum]
      exact ⟨1, by rw [CharTwo.sub_eq_add]; ring_nf⟩
    · have h2 : p.coeff 2 = 1 := h12 ▸ h1
      simp [Finset.sum_range_succ, h0, h1, h2] at hsum
      refine ⟨4, by norm_num, by norm_num, ?_⟩
      rw [hsum]
      exact ⟨X + 1, by rw [CharTwo.sub_eq_add]; ring_nf; try reduce_mod_char⟩
  · have h0 : p.coeff 0 = 1 := by
      have := hc 0 (by norm_num)
      simpa [hlead] using this
    have h13 : p.coeff 1 = p.coeff 3 := hc 1 (by norm_num)
    rcases zmod2_cases (p.coeff 2) with h2 | h2 <;> rcases zmod2_cases (p.coeff 3) with h3 | h3
    · have h1 : p.coeff 1 = 0 := h13 ▸ h3
      simp [Finset.sum_range_succ, h0, h1, h2, h3] at hsum
      refine ⟨4, by norm_num, by norm_num, ?_⟩
      rw [hsum]
      exact ⟨1, by rw [CharTwo.sub_eq_add]; ring_nf⟩
    · have h1 : p.coeff 1 = 1 := h13 ▸ h3
      simp [Finset.sum_range_succ, h0, h1, h2, h3] at hsum
      refine ⟨6, by norm_num, by norm_num, ?_⟩
      rw [hsum]
      exact ⟨X ^ 2 + X + 1, by rw [CharTwo.sub_eq_add]; ring_nf; try reduce_mod_char⟩
    · have h1 : p.coeff 1 = 0 := h13 ▸ h3
      simp [Finset.sum_range_succ, h0, h1, h2, h3] at hsum
      refine ⟨6, by norm_num, by norm_num, ?_⟩
      rw [hsum]
      exact ⟨X ^ 2 + 1, by rw [CharTwo.sub_eq_add]; ring_nf; try reduce_mod_char⟩
    · have h1 : p.coeff 1 = 1 := h13 ▸ h3
      simp [Finset.sum_range_succ, h0, h1, h2, h3] at hsum
      refine ⟨5, by norm_num, by norm_num, ?_⟩
      rw [hsum]
      exact ⟨X + 1, by rw [CharTwo.sub_eq_add]; ring_nf; try reduce_mod_char⟩

private theorem charpoly_inv_eq_reverse {d : ℕ} (A : Matrix (Fin d) (Fin d) (ZMod 2))
    (hA : IsUnit A) : A⁻¹.charpoly = A.charpoly.reverse := by
  have hdet : A.det = 1 := by
    have hu : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).1 hA
    generalize A.det = x at hu
    fin_cases x
    · exact absurd hu not_isUnit_zero
    · rfl
  rw [Matrix.charpoly_inv A hA, hdet, Matrix.reverse_charpoly]
  simp [Ring.inverse_one, CharTwo.neg_eq]

private theorem real_pow {d : ℕ} (hd : d ≤ 4) (g x : GL (Fin d) (ZMod 2))
    (hx : x * g * x⁻¹ = g⁻¹) : ∃ k, 1 ≤ k ∧ k ≤ 6 ∧ g ^ k = 1 := by
  set M : Matrix (Fin d) (Fin d) (ZMod 2) := (g : Matrix (Fin d) (Fin d) (ZMod 2)) with hM
  have hunit : IsUnit M := g.isUnit
  have hconj : M⁻¹.charpoly = M.charpoly := by
    have h1 : (↑(g⁻¹) : Matrix (Fin d) (Fin d) (ZMod 2)) = M⁻¹ := Matrix.coe_units_inv g
    have h2 := Matrix.charpoly_units_conj x M
    rw [← h1, ← hx, Units.val_mul, Units.val_mul, Matrix.coe_units_inv x]
    exact h2
  have hrev : M.charpoly.reverse = M.charpoly := by
    rw [← charpoly_inv_eq_reverse M hunit]
    exact hconj
  obtain ⟨k, hk1, hk6, hdvd⟩ := selfRecip_dvd (Matrix.charpoly_monic M)
    (by simpa using hd) hrev
  refine ⟨k, hk1, hk6, ?_⟩
  obtain ⟨q, hq⟩ := hdvd
  have h := Matrix.aeval_self_charpoly M
  have h0 : aeval M (X ^ k - 1 : (ZMod 2)[X]) = 0 := by rw [hq, map_mul, h, zero_mul]
  rw [map_sub, map_pow, aeval_X, map_one] at h0
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  exact sub_eq_zero.mp h0

end S16C1G47Four

open S16C1G47Four CFSG.SectionRank.Ccomm in
theorem s16c1_G47_g4 {E : Type*} [Group E] [Finite E] (hcomm : ∀ x y : E, x * y = y * x)
    (hE : ∀ x : E, x * x = 1) (hcard : Nat.card E ≤ 16) {a b : MulAut E} (ha : a * a = 1)
    (hb : b * b = 1) (hodd : Odd (orderOf (a * b))) :
    orderOf (a * b) = 1 ∨ orderOf (a * b) = 3 ∨ orderOf (a * b) = 5 := by
  have hP : IsPGroup 2 E := fun x => ⟨1, by simpa [pow_two] using hE x⟩
  obtain ⟨d, hd⟩ := hP.exists_card_eq
  have hd4 : d ≤ 4 := by
    by_contra h
    have h5 : 5 ≤ d := by omega
    have : 2 ^ 5 ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) h5
    omega
  obtain ⟨e⟩ := nonempty_mulEquiv_of_elementary (p := 2) hcomm
    (fun x => by simpa [pow_two] using hE x) hd
  let φ := elemAutEquivGL e
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have key : a * (a * b) * a⁻¹ = (a * b)⁻¹ := by
    rw [mul_inv_rev, hai, hbi, ← mul_assoc, ha, one_mul]
  have hx : φ a * φ (a * b) * (φ a)⁻¹ = (φ (a * b))⁻¹ := by
    have h := congrArg φ key
    simpa only [map_mul, map_inv] using h
  obtain ⟨k, hk1, hk6, hk⟩ := real_pow hd4 (φ (a * b)) (φ a) hx
  have hdvd : orderOf (a * b) ∣ k := by
    rw [← MulEquiv.orderOf_eq φ]
    exact orderOf_dvd_of_pow_eq_one hk
  obtain ⟨m, hm⟩ := hodd
  have hle : orderOf (a * b) ≤ k := Nat.le_of_dvd (by omega) hdvd
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
