module

public import CFSG.Timmesfeld.Orders.Distinct

public section

namespace CFSG.Timmesfeld.Orders

open CFSG.Open

private theorem ppd8_dvd_cancel {m n d : ℕ} (hn : 0 < n) (h : m * n ∣ n * d) : m ∣ d := by
  rw [mul_comm m n] at h
  exact Nat.dvd_of_mul_dvd_mul_left hn h

private theorem ppd8_sixteen_le (n : ℕ) (hn : 1 ≤ n) : 16 ≤ 16 * n :=
  calc 16 = 16 * 1 := by ring
    _ ≤ 16 * n := Nat.mul_le_mul_left 16 hn

private theorem ppd8_nine_le (k n : ℕ) (hk : 3 ≤ k) (hn : 1 ≤ n) : 27 ≤ 9 * k * n :=
  calc 27 = 9 * 3 * 1 := by norm_num
    _ ≤ 9 * k * n := Nat.mul_le_mul (Nat.mul_le_mul_left 9 hk) hn

private theorem ppd8_eighteen_le (k n : ℕ) (hk : 2 ≤ k) (hn : 1 ≤ n) : 36 ≤ 18 * k * n :=
  calc 36 = 18 * 2 * 1 := by norm_num
    _ ≤ 18 * k * n := Nat.mul_le_mul (Nat.mul_le_mul_left 18 hk) hn

private theorem ppd8_sixteen_not_dvd_list (d : ℕ)
    (hd : d ∈ [30, 24, 20, 18, 14, 12, 8, 2]) : ¬ 16 ∣ d := by
  intro h
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact absurd h (by decide)

private theorem ppd8_nine_mul_not_dvd_list (k d : ℕ) (hk : 3 ≤ k)
    (hd : d ∈ [30, 24, 20, 18, 14, 12, 8, 2]) : ¬ 9 * k ∣ d := by
  intro h
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    have hle := Nat.le_of_dvd (by norm_num) h
    have hk3 : k = 3 := by omega
    subst hk3
    exact absurd h (by decide)

private theorem ppd8_eighteen_mul_not_dvd_list (k d : ℕ) (hk : 2 ≤ k)
    (hd : d ∈ [30, 24, 20, 18, 14, 12, 8, 2]) : ¬ 18 * k ∣ d := by
  intro h
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    have hle := Nat.le_of_dvd (by norm_num) h
    omega

private theorem ppd8_dvd_ordE8_factors {r n k' : ℕ} (hr : IsPrimitivePrimeDivisor r k')
    (hk' : 0 < k') (h : r ∣ ordE8 (2 ^ n)) :
    ∃ d ∈ [30, 24, 20, 18, 14, 12, 8, 2], k' ∣ n * d := by
  have hr2 : r ≠ 2 := hr.ne_two hk'
  rw [ordE8] at h
  simp only [← pow_mul] at h
  rcases hr.prime.dvd_mul.mp h with h | h
  · rcases hr.prime.dvd_mul.mp h with h | h
    · rcases hr.prime.dvd_mul.mp h with h | h
      · rcases hr.prime.dvd_mul.mp h with h | h
        · rcases hr.prime.dvd_mul.mp h with h | h
          · rcases hr.prime.dvd_mul.mp h with h | h
            · rcases hr.prime.dvd_mul.mp h with h | h
              · rcases hr.prime.dvd_mul.mp h with h | h
                · exact absurd ((Nat.prime_dvd_prime_iff_eq hr.prime Nat.prime_two).mp
                    (hr.prime.dvd_of_dvd_pow h)) hr2
                · exact ⟨30, by decide, (hr.dvd_sub_one_iff hk' (n * 30)).mp h⟩
              · exact ⟨24, by decide, (hr.dvd_sub_one_iff hk' (n * 24)).mp h⟩
            · exact ⟨20, by decide, (hr.dvd_sub_one_iff hk' (n * 20)).mp h⟩
          · exact ⟨18, by decide, (hr.dvd_sub_one_iff hk' (n * 18)).mp h⟩
        · exact ⟨14, by decide, (hr.dvd_sub_one_iff hk' (n * 14)).mp h⟩
      · exact ⟨12, by decide, (hr.dvd_sub_one_iff hk' (n * 12)).mp h⟩
    · exact ⟨8, by decide, (hr.dvd_sub_one_iff hk' (n * 8)).mp h⟩
  · exact ⟨2, by decide, (hr.dvd_sub_one_iff hk' (n * 2)).mp h⟩

private theorem ppd8_prim_dvd_ordA {r f k i : ℕ} (hr : IsPrimitivePrimeDivisor r k) (hk : 0 < k)
    (hf : 1 ≤ f) (hi : i ∈ Finset.Icc 2 9) (hdiv : k ∣ f * i) :
    r ∣ ordA 8 (2 ^ f) := by
  have hcpos : 0 < 2 ^ f - 1 := by
    have h2 : 2 ≤ 2 ^ f := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  have hsq : (2 ^ f - 1) * (2 ^ f - 1) ∣
      ∏ j ∈ Finset.Icc 2 9, ((2 ^ f) ^ j - 1) := by
    have h23 : ({2, 3} : Finset ℕ) ⊆ Finset.Icc 2 9 := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_Icc]
      omega
    have h := Finset.prod_dvd_prod_of_subset _ _ (fun j => (2 ^ f) ^ j - 1) h23
    rw [Finset.prod_pair (by norm_num)] at h
    exact (mul_dvd_mul (Nat.sub_one_dvd_pow_sub_one _ 2)
      (Nat.sub_one_dvd_pow_sub_one _ 3)).trans h
  have hri : r ∣ (2 ^ f) ^ i - 1 := by
    simp only [← pow_mul]
    exact (hr.dvd_sub_one_iff hk (f * i)).mpr hdiv
  have hprod : r ∣ ∏ j ∈ Finset.Icc 2 9, ((2 ^ f) ^ j - 1) :=
    hri.trans (Finset.dvd_prod_of_mem (fun j => (2 ^ f) ^ j - 1) hi)
  have hiff := prime_dvd_div_iff (p := r)
    (P := (2 ^ f) ^ 36 * ∏ j ∈ Finset.Icc 2 9, ((2 ^ f) ^ j - 1))
    (c := 2 ^ f - 1) (d := Nat.gcd 9 (2 ^ f - 1)) hr.prime
    (Nat.gcd_dvd_right 9 (2 ^ f - 1))
    (dvd_mul_of_dvd_right hsq ((2 ^ f) ^ 36))
    (Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_right 9 (2 ^ f - 1)) hcpos)
  rw [ordA]
  exact hiff.mpr (dvd_mul_of_dvd_right hprod ((2 ^ f) ^ 36))

theorem ordA_eight_not_dvd_ordE8 {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k) :
    ¬ ordA 8 (2 ^ (n * k)) ∣ ordE8 (2 ^ n) := by
  intro hdvd
  rcases Nat.lt_or_ge k 3 with hk2 | hk3
  · have hk_eq : k = 2 := by omega
    subst hk_eq
    have hge : 16 ≤ 16 * n := ppd8_sixteen_le n hn
    obtain ⟨r, hr⟩ :=
      exists_isPrimitivePrimeDivisor (by omega : 2 ≤ 16 * n) (by omega : 16 * n ≠ 6)
    have hf : 1 ≤ n * 2 := by omega
    have hrA : r ∣ ordA 8 (2 ^ (n * 2)) :=
      ppd8_prim_dvd_ordA (i := 8) hr (by omega) hf (by norm_num [Finset.mem_Icc])
        ⟨1, by ring⟩
    have hrE : r ∣ ordE8 (2 ^ n) := hrA.trans hdvd
    obtain ⟨a, ha, hdiv⟩ := ppd8_dvd_ordE8_factors hr (by omega) hrE
    exact ppd8_sixteen_not_dvd_list a ha (ppd8_dvd_cancel (by omega) hdiv)
  · have hge : 27 ≤ 9 * k * n := ppd8_nine_le k n hk3 hn
    obtain ⟨r, hr⟩ :=
      exists_isPrimitivePrimeDivisor (by omega : 2 ≤ 9 * k * n) (by omega : 9 * k * n ≠ 6)
    have hf : 1 ≤ n * k := by
      have : 0 < n * k := Nat.mul_pos (by omega) (by omega)
      omega
    have hrA : r ∣ ordA 8 (2 ^ (n * k)) :=
      ppd8_prim_dvd_ordA (i := 9) hr (by omega) hf (by norm_num [Finset.mem_Icc])
        ⟨1, by ring⟩
    have hrE : r ∣ ordE8 (2 ^ n) := hrA.trans hdvd
    obtain ⟨a, ha, hdiv⟩ := ppd8_dvd_ordE8_factors hr (by omega) hrE
    exact ppd8_nine_mul_not_dvd_list k a hk3 ha (ppd8_dvd_cancel (by omega) hdiv)

theorem ordTwistedA_eight_not_dvd_ordE8 {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k) :
    ¬ ordTwistedA 8 (2 ^ (n * k)) ∣ ordE8 (2 ^ n) := by
  intro hdvd
  have hnk : 1 ≤ n * k := by
    have : 0 < n * k := Nat.mul_pos (by omega) (by omega)
    omega
  have hA := profile_ordTwistedA (n := 8) (g := n * k) (by norm_num) hnk
  have hge : 36 ≤ 18 * k * n := ppd8_eighteen_le k n hk hn
  obtain ⟨r, hr⟩ :=
    exists_isPrimitivePrimeDivisor (by omega : 2 ≤ 18 * k * n) (by omega : 18 * k * n ≠ 6)
  have hzU : zU 8 (n * k) (18 * k * n) := by
    have h := zU_top (n := 8) (g := n * k) (t := 4) (Or.inl (by norm_num)) (by norm_num)
      (Nat.mul_pos (by omega) (by omega))
    simpa [show 2 * (n * k * (2 * 4 + 1)) = 18 * k * n by ring] using h
  have hrA : r ∣ ordTwistedA 8 (2 ^ (n * k)) :=
    (hA.prim r (18 * k * n) hr (by omega)).mpr hzU
  have hrE : r ∣ ordE8 (2 ^ n) := hrA.trans hdvd
  obtain ⟨a, ha, hdiv⟩ := ppd8_dvd_ordE8_factors hr (by omega) hrE
  exact ppd8_eighteen_mul_not_dvd_list k a hk ha (ppd8_dvd_cancel (by omega) hdiv)

end CFSG.Timmesfeld.Orders

end
