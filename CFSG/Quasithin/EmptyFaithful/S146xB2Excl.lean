module

public import CFSG.Quasithin.EmptyFaithful.S146xB2Cmp
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdOrders
public import CFSG.LieType.Ree.SuzukiOrder

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1

section Arith

theorem eq_exp_of_two_pow_mul_odd_eq {s a u v : ℕ} (hu : Odd u) (hv : Odd v) (h : 2 ^ s * u = 2 ^ a * v) :
    s = a := by
  have key : ∀ {s a u v : ℕ}, Odd v → 2 ^ s * u = 2 ^ a * v → ¬ a < s := by
    intro s a u v hv h hlt
    obtain ⟨d, rfl⟩ : ∃ d, s = a + d + 1 := ⟨s - a - 1, by omega⟩
    have h2 : v = 2 ^ (d + 1) * u := by
      have : 2 ^ a * v = 2 ^ a * (2 ^ (d + 1) * u) := by
        rw [← h]
        ring
      exact Nat.eq_of_mul_eq_mul_left (by positivity) this
    have hev : Even (2 ^ (d + 1)) := Nat.even_pow.mpr ⟨even_two, by omega⟩
    have : Even v := by
      rw [h2]
      exact hev.mul_right u
    exact (Nat.not_even_iff_odd.mpr hv) this
  exact le_antisymm (not_lt.mp (key hv h)) (not_lt.mp (key hu h.symm))

theorem exists_two_pow_shape_of_fermatMersenne {p : ℕ} (hp : IsFermatOrMersennePrime p) (hp7 : 7 < p) :
    ∃ b o : ℕ, 3 ≤ b ∧ Odd o ∧ Odd p ∧
      ((p = 2 * 2 ^ b + 1 ∧ o = 2 ^ b + 1) ∨ (p + 1 = 2 * 2 ^ b ∧ o = 2 ^ b - 1)) := by
  obtain ⟨-, hF | ⟨k, -, hk⟩⟩ := hp
  · obtain ⟨k, hk⟩ := hF
    have hk2' : 2 ≤ k := by
      by_contra hlt
      have hk1 : k ≤ 1 := by omega
      have h1 : 2 ^ k ≤ 2 := by
        calc 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
          _ = 2 := by norm_num
      have h2 : 2 ^ 2 ^ k ≤ 4 := by
        calc 2 ^ 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) h1
          _ = 4 := by norm_num
      omega
    have h4 : 4 ≤ 2 ^ k := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2'
    have hb : 2 ^ 2 ^ k = 2 * 2 ^ (2 ^ k - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have hev : Even (2 ^ (2 ^ k - 1)) := Nat.even_pow.mpr ⟨even_two, by omega⟩
    have hpodd : Odd p := by
      rw [hk, hb]
      exact (even_two_mul _).add_one
    exact ⟨2 ^ k - 1, 2 ^ (2 ^ k - 1) + 1, by omega, hev.add_one, hpodd,
      Or.inl ⟨by rw [hk, hb], rfl⟩⟩
  · have hpos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have hk' : p + 1 = 2 ^ k := by omega
    have h4 : 4 ≤ k := by
      by_contra hlt
      have h1 : 2 ^ k ≤ 8 := by
        calc 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = 8 := by norm_num
      omega
    have hb : 2 ^ k = 2 * 2 ^ (k - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have hev : Even (2 ^ (k - 1)) := Nat.even_pow.mpr ⟨even_two, by omega⟩
    have hpos' : 1 ≤ 2 ^ (k - 1) := Nat.one_le_two_pow
    obtain ⟨j, hj⟩ := hev
    exact ⟨k - 1, 2 ^ (k - 1) - 1, by omega, ⟨j - 1, by omega⟩, ⟨2 * j - 1, by omega⟩,
      Or.inr ⟨by omega, rfl⟩⟩

end Arith

section Orders

theorem card_of_isPSL_two_even {N : Type} [Group N] {n : ℕ} (hn : 1 ≤ n) (h : IsPSL 2 2 n N) :
    Nat.card N = 2 ^ n * (4 ^ n - 1) := by
  obtain ⟨-, K, hF, hFin, hK, ⟨e⟩⟩ := h
  rw [Nat.card_congr
      (e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm).toEquiv,
    CFSG.OrderReductions.LinearOrders.card_projectiveSpecialLinear K 2 (by norm_num), hK]
  have hodd : Odd (2 ^ n - 1) := by
    have h1 : 2 ^ n % 2 = 0 := by
      rcases Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0) with ⟨k, rfl⟩
      rw [pow_succ]; omega
    have h2 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    rw [Nat.odd_iff]; omega
  have hg : Nat.gcd 2 (2 ^ n - 1) = 1 := (Nat.coprime_two_left.mpr hodd)
  rw [hg]
  have : (2 ^ n) ^ 2 = 4 ^ n := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  simp [this]

theorem not_three_dvd_card_of_isSz_model {N : Type} [Group N] {n : ℕ}
    (h : IsSz n N) : ¬ 3 ∣ Nat.card N := by
  obtain ⟨-, a, -, K, _, _, hf, hK, ⟨e⟩⟩ := h
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hf]
  rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK']
  have hq : 2 ^ (2 * a + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  generalize 2 ^ (2 * a + 1) = q at hq ⊢
  have hq1 : 1 ≤ q := by omega
  intro hd
  have hmod : (q ^ 2 * (q - 1) * (q ^ 2 + 1)) % 3 = 2 := by
    have h1 : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hq]
    have h2 : (q - 1) % 3 = 1 := by omega
    have h3 : (q ^ 2 + 1) % 3 = 2 := by omega
    rw [Nat.mul_mod, Nat.mul_mod (q ^ 2), h1, h2, h3]
  omega

end Orders

section Excl

variable {N : Type} [Group N] [Finite N]

theorem three_dvd_card_of_shape
    (hshape : (∃ p : ℕ, IsFermatOrMersennePrime p ∧ 7 < p ∧ IsPSL 2 p 1 N) ∨ IsPSL 3 2 1 N ∨
      IsAlt 6 N ∨ IsPSL 3 3 1 N) : 3 ∣ Nat.card N := by
  rcases hshape with ⟨p, hp, hp7, hpsl⟩ | h32 | hA6 | h33
  · exact three_dvd_card_of_isPSL_two hp.1 (by omega) hpsl
  · rw [CFSG.QuasithinUnique.Id2519.card_of_psl_three_two h32]; norm_num
  · obtain ⟨e⟩ := hA6
    rw [Nat.card_congr e.toEquiv, CFSG.QuasithinUnique.Id2519.card_alternatingGroup_six]; norm_num
  · rw [CFSG.QuasithinUnique.Id2519.card_of_psl_three h33]
    decide

theorem false_of_bender_of_shape {n : ℕ} (hn : 2 ≤ n)
    (hB : IsPSL 2 2 n N ∨ IsSz n N)
    (hshape : (∃ p : ℕ, IsFermatOrMersennePrime p ∧ 7 < p ∧ IsPSL 2 p 1 N) ∨ IsPSL 3 2 1 N ∨
      IsAlt 6 N ∨ IsPSL 3 3 1 N) : False := by
  rcases hB with hL | hSz
  · have hc := card_of_isPSL_two_even (by omega) hL
    have hmono : 5 ≤ n → 5616 < 2 ^ n * (4 ^ n - 1) := by
      intro h5
      have h1 : 2 ^ 5 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h5
      have h2 : 4 ^ 5 ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) h5
      calc 5616 < 32 * 1023 := by norm_num
        _ ≤ 2 ^ n * (4 ^ n - 1) := Nat.mul_le_mul (by simpa using h1) (by omega)
    have hne : ∀ c : ℕ, c ≤ 5616 → c ≠ 60 → c ≠ 504 → c ≠ 4080 → 2 ^ n * (4 ^ n - 1) ≠ c := by
      intro c hc1 h60 h504 h4080 hcc
      by_cases h5 : 5 ≤ n
      · have := hmono h5
        omega
      · have : n = 2 ∨ n = 3 ∨ n = 4 := by omega
        rcases this with rfl | rfl | rfl <;> norm_num at hcc <;> omega
    rcases hshape with ⟨p, hp, hp7, hpsl⟩ | h32 | hA6 | h33
    ·
      obtain ⟨b, o, hb3, ho, hpodd, hshp⟩ := exists_two_pow_shape_of_fermatMersenne hp hp7
      have hpp : p.Prime := hp.1
      have : Fact p.Prime := ⟨hpp⟩
      obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_psl2_model hpsl
      have hcN : Nat.card N = p * (p ^ 2 - 1) / 2 := by
        rw [Nat.card_congr e.toEquiv,
          CFSG.GorensteinWalter.psl2_card_formula F
            (CFSG.QuasithinUnique.Out21.hodd_of (by omega) hF), hF]
      obtain ⟨u, hu⟩ : ∃ u, u = 2 ^ b := ⟨_, rfl⟩
      have hu8 : 8 ≤ u := by
        rw [hu]
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb3
      rw [← hu] at hshp
      have hN2 : Nat.card N = p * (2 * u) * o := by
        rw [hcN]
        apply Nat.div_eq_of_eq_mul_left (by norm_num)
        rcases hshp with ⟨hp', ho'⟩ | ⟨hp', ho'⟩
        · have hsq : p ^ 2 - 1 = 4 * u ^ 2 + 4 * u :=
            Nat.sub_eq_of_eq_add (by rw [hp']; ring)
          rw [hsq, ho']
          ring
        · obtain ⟨m, hm⟩ : ∃ m, u = m + 1 := ⟨u - 1, by omega⟩
          have hom : o = m := by omega
          have hpm : p = 2 * m + 1 := by omega
          have hsq : p ^ 2 - 1 = 4 * m ^ 2 + 4 * m :=
            Nat.sub_eq_of_eq_add (by rw [hpm]; ring)
          rw [hsq, hom, hm]
          ring
      have h1 : 2 ^ n * (4 ^ n - 1) = 2 ^ (b + 1) * (p * o) := by
        rw [← hc, hN2, pow_succ, ← hu]
        ring
      have hodd4 : Odd (4 ^ n - 1) := by
        have h1' : 4 ^ n % 2 = 0 := by
          rcases Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0) with ⟨k, rfl⟩
          rw [pow_succ]; omega
        have h2' : 1 ≤ 4 ^ n := Nat.one_le_pow _ _ (by norm_num)
        rw [Nat.odd_iff]; omega
      have hn' : n = b + 1 := eq_exp_of_two_pow_mul_odd_eq hodd4 (hpodd.mul ho) h1
      subst hn'
      have h2 : 4 ^ (b + 1) - 1 = p * o := by
        have h3 : 2 ^ (b + 1) * (4 ^ (b + 1) - 1) = 2 ^ (b + 1) * (p * o) := h1
        exact Nat.eq_of_mul_eq_mul_left (by positivity) h3
      have h4 : 4 ^ (b + 1) = 4 * u ^ 2 := by
        rw [hu, pow_succ, ← pow_mul, mul_comm b 2, pow_mul]
        norm_num
        ring
      rw [h4] at h2
      have hpos : 1 ≤ 4 * u ^ 2 := by nlinarith
      have h2' : 4 * u ^ 2 = p * o + 1 := by omega
      rcases hshp with ⟨hp', ho'⟩ | ⟨hp', ho'⟩
      · rw [hp', ho'] at h2'
        nlinarith
      · obtain ⟨m, hm⟩ : ∃ m, u = m + 1 := ⟨u - 1, by omega⟩
        have hom : o = m := by omega
        have hpm : p = 2 * m + 1 := by omega
        rw [hpm, hom, hm] at h2'
        nlinarith
    · rw [CFSG.QuasithinUnique.Id2519.card_of_psl_three_two h32] at hc
      exact hne 168 (by norm_num) (by norm_num) (by norm_num) (by norm_num) hc.symm
    · obtain ⟨e⟩ := hA6
      rw [Nat.card_congr e.toEquiv, CFSG.QuasithinUnique.Id2519.card_alternatingGroup_six] at hc
      exact hne 360 (by norm_num) (by norm_num) (by norm_num) (by norm_num) hc.symm
    · rw [CFSG.QuasithinUnique.Id2519.card_of_psl_three h33] at hc
      have h5616 : ((3 ^ 1) ^ (3 * (3 - 1) / 2) * ∏ index ∈ Finset.Icc 2 3, ((3 ^ 1) ^ index - 1)) /
          Nat.gcd 3 (3 ^ 1 - 1) = 5616 := by decide
      rw [h5616] at hc
      exact hne 5616 (by norm_num) (by norm_num) (by norm_num) (by norm_num) hc.symm
  · exact not_three_dvd_card_of_isSz_model hSz (three_dvd_card_of_shape hshape)

end Excl


end CFSG.Quasithin
