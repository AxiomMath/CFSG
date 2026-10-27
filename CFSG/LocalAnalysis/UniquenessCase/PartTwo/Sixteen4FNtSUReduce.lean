module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtSUTorus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

theorem s16nt_su_supp_reduce {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4)
    {n : ℕ} {a : Fin n → K} (ha : 4 ≤ (Function.support a).ncard) :
    ∃ w : Fin n → K, (Function.support w).ncard = 4 ∧ herm (s16ntSuSigma K) w w = 0 ∧
      herm (s16ntSuSigma K) w a = 1 ∧
      (Function.support (a + w)).ncard < (Function.support a).ncard := by
  classical
  obtain ⟨ω, hω0, hω1, hω_eq⟩ := s16nt_su_exists_omega hK
  have hω2_ne_zero : ω ^ 2 ≠ 0 := pow_ne_zero 2 hω0
  have hω_ne_zero : ω ≠ 0 := hω0
  have hω3 : ω ^ 3 = 1 := s16nt_su_pow_three hK hω0
  have hω_add : ω + ω ^ 2 = 1 := by
    rw [← CharTwo.add_eq_zero]
    rw [add_comm ω (ω ^ 2)]
    exact hω_eq
  have hω_add1 : 1 + ω ^ 2 = ω := by
    rw [← CharTwo.add_eq_zero]
    rw [add_comm 1 (ω ^ 2), add_assoc, add_comm 1 ω, ← add_assoc]
    exact hω_eq
  have hω_add2 : 1 + ω = ω ^ 2 := by
    rw [← CharTwo.add_eq_zero]
    rw [add_comm 1 ω, add_assoc, add_comm 1 (ω ^ 2), ← add_assoc, add_comm ω (ω ^ 2)]
    exact hω_eq
  obtain ⟨I, hI_sub, hI_card⟩ := Set.exists_subset_card_eq ha
  obtain ⟨i1, i2, i3, i4, h12, h13, h14, h23, h24, h34, hI_eq⟩ :=
    (Set.ncard_eq_four (s := I)).mp hI_card
  have ha_i1 : a i1 ≠ 0 := by
    have h : i1 ∈ Function.support a := hI_sub (by rw [hI_eq]; simp)
    simpa [Function.mem_support] using h
  have ha_i2 : a i2 ≠ 0 := by
    have h : i2 ∈ Function.support a := hI_sub (by rw [hI_eq]; simp)
    simpa [Function.mem_support] using h
  have ha_i3 : a i3 ≠ 0 := by
    have h : i3 ∈ Function.support a := hI_sub (by rw [hI_eq]; simp)
    simpa [Function.mem_support] using h
  have ha_i4 : a i4 ≠ 0 := by
    have h : i4 ∈ Function.support a := hI_sub (by rw [hI_eq]; simp)
    simpa [Function.mem_support] using h
  let w : Fin n → K := Pi.single i1 (a i1) + Pi.single i2 (a i2) +
    Pi.single i3 (ω ^ 2 * a i3) + Pi.single i4 (ω * a i4)
  have hw1 : w i1 = a i1 := by simp [w, Pi.single_apply, h12.symm, h13.symm, h14.symm]
  have hw2 : w i2 = a i2 := by simp [w, Pi.single_apply, h12, h23.symm, h24.symm]
  have hw3 : w i3 = ω ^ 2 * a i3 := by simp [w, Pi.single_apply, h13, h23, h34.symm]
  have hw4 : w i4 = ω * a i4 := by simp [w, Pi.single_apply, h14, h24, h34]
  have hsupp : Function.support w = I := by
    ext k
    simp only [Function.mem_support, hI_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    by_cases hk1 : k = i1
    · rw [hk1]; simp [hw1, ha_i1]
    by_cases hk2 : k = i2
    · rw [hk2]; simp [hw2, ha_i2]
    by_cases hk3 : k = i3
    · rw [hk3]; simp [hw3, mul_ne_zero hω2_ne_zero ha_i3]
    by_cases hk4 : k = i4
    · rw [hk4]; simp [hw4, mul_ne_zero hω_ne_zero ha_i4]
    · have hw0 : w k = 0 := by simp [w, Pi.single_apply, hk1, hk2, hk3, hk4]
      simp [hw0, hk1, hk2, hk3, hk4]
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · rw [hsupp, hI_card]
  · have hsum : (∑ k : Fin n, s16ntSuSigma K (w k) * w k) =
        s16ntSuSigma K (w i1) * w i1 + s16ntSuSigma K (w i2) * w i2 +
        s16ntSuSigma K (w i3) * w i3 + s16ntSuSigma K (w i4) * w i4 := by
      have hsub : ({i1, i2, i3, i4} : Finset (Fin n)) ⊆ Finset.univ := by simp
      have hzero : ∀ x ∈ Finset.univ, x ∉ ({i1, i2, i3, i4} : Finset (Fin n)) →
          s16ntSuSigma K (w x) * w x = 0 := by
        intro x _ hx
        have hx' : x ∉ Function.support w := by
          rw [hsupp, hI_eq]
          simpa using hx
        have hw0 : w x = 0 := by simpa [Function.mem_support] using hx'
        rw [hw0, mul_zero]
      rw [← Finset.sum_subset hsub hzero]
      simp [Finset.sum_insert, h12, h13, h14, h23, h24, h34]
      ring
    rw [herm, hsum]
    rw [hw1, hw2, hw3, hw4]
    have h1 : s16ntSuSigma K (a i1) * a i1 = 1 := s16nt_su_norm_one hK ha_i1
    have h2 : s16ntSuSigma K (a i2) * a i2 = 1 := s16nt_su_norm_one hK ha_i2
    have h3 : s16ntSuSigma K (ω ^ 2 * a i3) * (ω ^ 2 * a i3) = 1 := by
      rw [map_mul]
      calc s16ntSuSigma K (ω ^ 2) * s16ntSuSigma K (a i3) * (ω ^ 2 * a i3)
          = s16ntSuSigma K (ω ^ 2) * ω ^ 2 * (s16ntSuSigma K (a i3) * a i3) := by ring
        _ = 1 * 1 := by rw [s16nt_su_norm_one hK hω2_ne_zero, s16nt_su_norm_one hK ha_i3]
        _ = 1 := by rw [one_mul]
    have h4 : s16ntSuSigma K (ω * a i4) * (ω * a i4) = 1 := by
      rw [map_mul]
      calc s16ntSuSigma K ω * s16ntSuSigma K (a i4) * (ω * a i4)
          = s16ntSuSigma K ω * ω * (s16ntSuSigma K (a i4) * a i4) := by ring
        _ = 1 * 1 := by rw [s16nt_su_norm_one hK hω_ne_zero, s16nt_su_norm_one hK ha_i4]
        _ = 1 := by rw [one_mul]
    rw [h1, h2, h3, h4]
    rw [CharTwo.add_self_eq_zero, zero_add, CharTwo.add_self_eq_zero]
  · have hsum : (∑ k : Fin n, s16ntSuSigma K (w k) * a k) =
        s16ntSuSigma K (w i1) * a i1 + s16ntSuSigma K (w i2) * a i2 +
        s16ntSuSigma K (w i3) * a i3 + s16ntSuSigma K (w i4) * a i4 := by
      have hsub : ({i1, i2, i3, i4} : Finset (Fin n)) ⊆ Finset.univ := by simp
      have hzero : ∀ x ∈ Finset.univ, x ∉ ({i1, i2, i3, i4} : Finset (Fin n)) →
          s16ntSuSigma K (w x) * a x = 0 := by
        intro x _ hx
        have hx' : x ∉ Function.support w := by
          rw [hsupp, hI_eq]
          simpa using hx
        have hw0 : w x = 0 := by simpa [Function.mem_support] using hx'
        rw [hw0, map_zero, zero_mul]
      rw [← Finset.sum_subset hsub hzero]
      simp [Finset.sum_insert, h12, h13, h14, h23, h24, h34]
      ring
    rw [herm, hsum]
    rw [hw1, hw2, hw3, hw4]
    have h1 : s16ntSuSigma K (a i1) * a i1 = 1 := s16nt_su_norm_one hK ha_i1
    have h2 : s16ntSuSigma K (a i2) * a i2 = 1 := s16nt_su_norm_one hK ha_i2
    have hσ_ω2 : s16ntSuSigma K (ω ^ 2) = ω := by
      rw [s16nt_su_sigma_apply]
      calc (ω ^ 2) ^ 2 = ω ^ 4 := by ring
        _ = ω ^ 3 * ω := by ring
        _ = 1 * ω := by rw [hω3]
        _ = ω := by rw [one_mul]
    have hσ_ω : s16ntSuSigma K ω = ω ^ 2 := s16nt_su_sigma_apply ω
    have h3 : s16ntSuSigma K (ω ^ 2 * a i3) * a i3 = ω := by
      rw [map_mul, hσ_ω2]
      rw [mul_assoc, s16nt_su_norm_one hK ha_i3, mul_one]
    have h4 : s16ntSuSigma K (ω * a i4) * a i4 = ω ^ 2 := by
      rw [map_mul, hσ_ω]
      rw [mul_assoc, s16nt_su_norm_one hK ha_i4, mul_one]
    rw [h1, h2, h3, h4]
    rw [CharTwo.add_self_eq_zero, zero_add, hω_add]
  · have hsupp_aw : Function.support (a + w) = Function.support a \ {i1, i2} := by
      ext k
      simp only [Function.mem_support, Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff]
      by_cases hk1 : k = i1
      · rw [hk1]
        have haw1 : (a + w) i1 = 0 := by simp [Pi.add_apply, hw1, CharTwo.add_self_eq_zero]
        rw [haw1]
        simp [ha_i1]
      by_cases hk2 : k = i2
      · rw [hk2]
        have haw2 : (a + w) i2 = 0 := by simp [Pi.add_apply, hw2, CharTwo.add_self_eq_zero]
        rw [haw2]
        simp [ha_i2]
      by_cases hk3 : k = i3
      · rw [hk3]
        have haw3 : (a + w) i3 = ω * a i3 := by
          simp [Pi.add_apply, hw3]
          calc a i3 + ω ^ 2 * a i3 = (1 + ω ^ 2) * a i3 := by ring
            _ = ω * a i3 := by rw [hω_add1]
        rw [haw3]
        have hk_supp : i3 ∈ Function.support a := hI_sub (by rw [hI_eq]; simp)
        have ha_i3' : a i3 ≠ 0 := by simpa [Function.mem_support] using hk_supp
        simp [mul_ne_zero hω_ne_zero ha_i3', ha_i3', h13.symm, h23.symm]
      by_cases hk4 : k = i4
      · rw [hk4]
        have haw4 : (a + w) i4 = ω ^ 2 * a i4 := by
          simp [Pi.add_apply, hw4]
          calc a i4 + ω * a i4 = (1 + ω) * a i4 := by ring
            _ = ω ^ 2 * a i4 := by rw [hω_add2]
        rw [haw4]
        have hk_supp : i4 ∈ Function.support a := hI_sub (by rw [hI_eq]; simp)
        have ha_i4' : a i4 ≠ 0 := by simpa [Function.mem_support] using hk_supp
        simp [mul_ne_zero hω2_ne_zero ha_i4', ha_i4', h14.symm, h24.symm]
      · have hw0 : w k = 0 := by simp [w, Pi.single_apply, hk1, hk2, hk3, hk4]
        have haw : (a + w) k = a k := by simp [Pi.add_apply, hw0, add_zero]
        rw [haw]
        simp [hk1, hk2]
    rw [hsupp_aw]
    have hsub : ({i1, i2} : Set (Fin n)) ⊆ Function.support a := by
      intro x hx
      simp at hx
      rcases hx with rfl | rfl
      · exact hI_sub (by rw [hI_eq]; simp)
      · exact hI_sub (by rw [hI_eq]; simp)
    rw [Set.ncard_sdiff hsub, Set.ncard_pair h12]
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
