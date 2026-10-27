module

public import CFSG.Timmesfeld.Orders.Distinct

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Orders

theorem index_of_prim_dvd_ordTwistedF4 {f p k : ℕ} (hp : IsPrimitivePrimeDivisor p k)
    (hk : 0 < k) (h : p ∣ ordTwistedF4 (2 ^ f)) :
    (k ∣ f * 12 ∧ ¬ k ∣ f * 6) ∨ k ∣ f * 4 ∨ (k ∣ f * 6 ∧ ¬ k ∣ f * 3) ∨ k ∣ f := by
  have hp2 := hp.ne_two hk
  unfold ordTwistedF4 at h
  rcases hp.prime.dvd_mul.1 h with h1 | h1
  · rcases hp.prime.dvd_mul.1 h1 with h2 | h2
    · rcases hp.prime.dvd_mul.1 h2 with h3 | h3
      · rcases hp.prime.dvd_mul.1 h3 with h4 | h4
        · exfalso
          have h5 : p ∣ 2 ^ (f * 12) := by rwa [pow_mul]
          exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.prime Nat.prime_two).1
            (hp.prime.dvd_of_dvd_pow h5))
        · left
          have h5 := (PrimDiv.dvd_pow_add_one_iff hp hk f 6).1 h4
          rw [show 2 * (f * 6) = f * 12 by ring] at h5
          exact h5
      · right; left
        exact (PrimDiv.dvd_pow_sub_one_iff hp hk f 4).1 h3
    · right; right; left
      have h5 := (PrimDiv.dvd_pow_add_one_iff hp hk f 3).1 h2
      rw [show 2 * (f * 3) = f * 6 by ring] at h5
      exact h5
  · right; right; right
    exact (hp.dvd_sub_one_iff hk f).1 h1

theorem gcd_dvd_numerator_ordA (m q : ℕ) (hm : 1 ≤ m) :
    Nat.gcd (m + 1) (q - 1) ∣
      q ^ (m * (m + 1) / 2) * ∏ j ∈ Finset.Icc 2 (m + 1), (q ^ j - 1) := by
  refine (Nat.gcd_dvd_right _ _).trans (Dvd.dvd.mul_left ?_ _)
  have h2 : q - 1 ∣ q ^ 2 - 1 := by simpa using Nat.sub_one_dvd_pow_sub_one q 2
  exact h2.trans
    (Finset.dvd_prod_of_mem (fun j => q ^ j - 1) (by simp only [Finset.mem_Icc]; omega))

theorem prim_dvd_ordA {m n i p : ℕ} (hn : 1 ≤ n) (hi2 : 2 ≤ i) (him : i ≤ m + 1)
    (hp : IsPrimitivePrimeDivisor p (n * i)) : p ∣ ordA m (2 ^ n) := by
  have hk : 0 < n * i := by positivity
  have hm : 1 ≤ m := by omega
  unfold ordA
  set q := 2 ^ n with hq
  have hq1 : 1 ≤ q - 1 := by
    have : 2 ≤ q := Nat.le_self_pow (by omega : n ≠ 0) 2
    omega
  have hpX : p ∣ q ^ (m * (m + 1) / 2) * ∏ j ∈ Finset.Icc 2 (m + 1), (q ^ j - 1) := by
    apply Dvd.dvd.mul_left
    exact ((PrimDiv.dvd_pow_sub_one_iff hp hk n i).2 dvd_rfl).trans
      (Finset.dvd_prod_of_mem (fun j => q ^ j - 1) (by simp only [Finset.mem_Icc]; omega))
  have hpg : ¬ p ∣ Nat.gcd (m + 1) (q - 1) := fun h => by
    have h1 := (hp.dvd_sub_one_iff hk n).1 (h.trans (Nat.gcd_dvd_right _ _))
    have h2 := Nat.le_of_dvd (by omega) h1
    nlinarith
  obtain ⟨c, hc⟩ := gcd_dvd_numerator_ordA m q hm
  rw [hc, Nat.mul_div_cancel_left _ (Nat.gcd_pos_of_pos_right _ (by omega))]
  rw [hc] at hpX
  exact ((Nat.Prime.dvd_mul hp.prime).1 hpX).resolve_left hpg

theorem index_of_prim_dvd_ordA {m n p k : ℕ} (hm : 1 ≤ m) (hp : IsPrimitivePrimeDivisor p k)
    (hk : 0 < k) (h : p ∣ ordA m (2 ^ n)) : ∃ i ∈ Finset.Icc 2 (m + 1), k ∣ n * i := by
  have hp2 := hp.ne_two hk
  unfold ordA at h
  have h' := h.trans (Nat.div_dvd_of_dvd (gcd_dvd_numerator_ordA m (2 ^ n) hm))
  rcases hp.prime.dvd_mul.1 h' with h1 | h1
  · exfalso
    have h2 : p ∣ 2 := hp.prime.dvd_of_dvd_pow (hp.prime.dvd_of_dvd_pow h1)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.prime Nat.prime_two).1 h2)
  · obtain ⟨i, hi, hpi⟩ := ((Nat.Prime.prime hp.prime).dvd_finsetProd_iff _).1 h1
    exact ⟨i, hi, (PrimDiv.dvd_pow_sub_one_iff hp hk n i).1 hpi⟩

theorem not_eight_mul_dvd {f c : ℕ} (hf : 1 ≤ f) (hc : c = 12 ∨ c = 4 ∨ c = 6 ∨ c = 1) :
    ¬ f * 8 ∣ f * c := by
  intro h
  obtain ⟨d, hd⟩ := h
  have h1 : c = 8 * d := by
    have h2 : f * c = f * (8 * d) := by rw [hd]; ring
    exact Nat.eq_of_mul_eq_mul_left (by omega) h2
  omega

theorem ordTwistedF4_ne_ordA {f m n : ℕ} (hf : 1 ≤ f) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ordTwistedF4 (2 ^ f) ≠ ordA m (2 ^ n) := by
  intro heq
  have hN : f * 12 = n * (m * (m + 1) / 2) := by
    obtain ⟨r, hr, h1⟩ := (profile_ordTwistedF4 hf).two
    obtain ⟨r', hr', h2⟩ := (profile_ordA hm hn).two
    exact eq_of_two_pow_mul_odd hr hr' (h1.symm.trans (heq.trans h2))
  obtain ⟨p, hp⟩ := exists_isPrimitivePrimeDivisor (k := f * 12) (by omega) (by omega)
  have hp1 : p ∣ ordTwistedF4 (2 ^ f) := by
    have h6 : p ∣ (2 ^ f) ^ 6 + 1 := (PrimDiv.dvd_pow_add_one_iff hp (by omega) f 6).2
      ⟨⟨1, by ring⟩, Nat.not_dvd_of_pos_of_lt (by omega) (by omega)⟩
    unfold ordTwistedF4
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_left h6 _) _) _) _
  rw [heq] at hp1
  obtain ⟨i, hi, hki⟩ := index_of_prim_dvd_ordA hm hp (by omega) hp1
  simp only [Finset.mem_Icc] at hi
  have h12 : f * 12 ≤ n * (m + 1) :=
    (Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) hki).trans (Nat.mul_le_mul_left _ hi.2)
  obtain ⟨p', hp'⟩ := exists_isPrimitivePrimeDivisor (k := n * (m + 1)) (by nlinarith)
    (by omega)
  have hp'1 : p' ∣ ordA m (2 ^ n) := prim_dvd_ordA hn (by omega) le_rfl hp'
  rw [← heq] at hp'1
  have hle : n * (m + 1) ≤ f * 12 := by
    rcases index_of_prim_dvd_ordTwistedF4 hp' (by positivity) hp'1 with ⟨h, -⟩ | h | ⟨h, -⟩ | h
    · exact Nat.le_of_dvd (by omega) h
    · exact (Nat.le_of_dvd (by omega) h).trans (by omega)
    · exact (Nat.le_of_dvd (by omega) h).trans (by omega)
    · exact (Nat.le_of_dvd (by omega) h).trans (by omega)
  have e1 : n * (m + 1) = f * 12 := le_antisymm hle h12
  have hmm : m * (m + 1) / 2 = m + 1 := by
    have h1 : n * (m * (m + 1) / 2) = n * (m + 1) := by rw [e1]; exact hN.symm
    exact Nat.eq_of_mul_eq_mul_left (by omega) h1
  have hm2 : m = 2 := by
    rcases Nat.lt_or_ge m 3 with h3 | h3
    · interval_cases m <;> omega
    · exfalso
      have h4 : 2 * (m + 1) + 2 ≤ m * (m + 1) := by nlinarith
      generalize m * (m + 1) = t at hmm h4
      omega
  subst hm2
  have hn4 : n = f * 4 := by omega
  obtain ⟨p'', hp''⟩ := exists_isPrimitivePrimeDivisor (k := n * 2) (by omega) (by omega)
  have h3 : p'' ∣ ordA 2 (2 ^ n) := prim_dvd_ordA hn le_rfl (by omega) hp''
  rw [← heq] at h3
  have e8 : n * 2 = f * 8 := by rw [hn4]; ring
  rw [e8] at hp''
  rcases index_of_prim_dvd_ordTwistedF4 hp'' (by omega) h3 with ⟨h, -⟩ | h | ⟨h, -⟩ | h
  · exact not_eight_mul_dvd hf (Or.inl rfl) h
  · exact not_eight_mul_dvd hf (Or.inr (Or.inl rfl)) h
  · exact not_eight_mul_dvd hf (Or.inr (Or.inr (Or.inl rfl))) h
  · exact not_eight_mul_dvd hf (Or.inr (Or.inr (Or.inr rfl))) (by rwa [mul_one])

theorem ordTwistedF4_ne_ordG2 {f n : ℕ} (hf : Odd f) (hn : 1 ≤ n) :
    ordTwistedF4 (2 ^ f) ≠ ordG2 (2 ^ n) := by
  intro heq
  have hf1 : 1 ≤ f := hf.pos
  have hN : f * 12 = n * 6 := by
    obtain ⟨r, hr, h1⟩ := (profile_ordTwistedF4 hf1).two
    obtain ⟨r', hr', h2⟩ := (profile_ordG2 hn).two
    exact eq_of_two_pow_mul_odd hr hr' (h1.symm.trans (heq.trans h2))
  have hn2 : n = f * 2 := by omega
  have hf2 : f ≠ 2 := by
    rintro rfl
    exact (Nat.not_odd_iff_even.mpr even_two) hf
  obtain ⟨p, hp⟩ := exists_isPrimitivePrimeDivisor (k := f * 3) (by omega) (by omega)
  have h1 : p ∣ ordG2 (2 ^ n) := by
    rw [ordG2_eq]
    apply Dvd.dvd.mul_left
    apply Dvd.dvd.mul_right
    exact (PrimDiv.dvd_pow_sub_one_iff hp (by omega) n 6).2 ⟨4, by rw [hn2]; ring⟩
  rw [← heq] at h1
  rcases index_of_prim_dvd_ordTwistedF4 hp (by omega) h1 with ⟨-, h⟩ | h | ⟨-, h⟩ | h
  · exact h ⟨2, by ring⟩
  · obtain ⟨d, hd⟩ := h
    have h2 : 4 = 3 * d := Nat.eq_of_mul_eq_mul_left (by omega : 0 < f) (by rw [hd]; ring)
    omega
  · exact h dvd_rfl
  · have := Nat.le_of_dvd (by omega) h
    omega

end CFSG.Quasithin.Vol2.Ch11.SecB
