module

public import CFSG.Quasithin.EmptyFaithful.T1515dB
public import CFSG.Quasithin.Vol2.Ch7Prop711Grp

public section

namespace CFSG.Quasithin.H13.Ch9.FFB

open CFSG.Assembly.LowTwoRank CFSG.Quasithin

theorem eq_of_two_pow_mul_odd : ∀ {a b x y : ℕ}, Odd x → Odd y → 2 ^ a * x = 2 ^ b * y →
    a = b ∧ x = y
  | 0, 0, x, y, _, _, h => ⟨rfl, by simpa using h⟩
  | 0, b + 1, x, y, hx, _, h => by
    exfalso
    rw [pow_zero, one_mul] at h
    rw [h] at hx
    exact (Nat.not_even_iff_odd.mpr hx)
      (Nat.even_mul.mpr (Or.inl (Nat.even_pow.mpr ⟨even_two, Nat.succ_ne_zero b⟩)))
  | a + 1, 0, x, y, _, hy, h => by
    exfalso
    rw [pow_zero, one_mul] at h
    rw [← h] at hy
    exact (Nat.not_even_iff_odd.mpr hy)
      (Nat.even_mul.mpr (Or.inl (Nat.even_pow.mpr ⟨even_two, Nat.succ_ne_zero a⟩)))
  | a + 1, b + 1, x, y, hx, hy, h => by
    have h' : 2 ^ a * x = 2 ^ b * y := by
      rw [pow_succ, pow_succ, mul_comm (2 ^ a) 2, mul_comm (2 ^ b) 2, mul_assoc, mul_assoc] at h
      exact Nat.eq_of_mul_eq_mul_left two_pos h
    obtain ⟨rfl, rfl⟩ := eq_of_two_pow_mul_odd hx hy h'
    exact ⟨rfl, rfl⟩

theorem odd_pow_sub_one {m n : ℕ} (hm : Even m) (hm0 : m ≠ 0) (hn : n ≠ 0) : Odd (m ^ n - 1) :=
  Nat.Even.sub_odd (Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hm0)) (Nat.even_pow.mpr ⟨hm, hn⟩)
    odd_one

theorem pow_two_mul (n j : ℕ) : 2 ^ (j * n) = (2 ^ n) ^ j := by
  rw [← pow_mul, mul_comm]

theorem pow_eq_pow_pow (n m j : ℕ) (hm : m = 2 ^ j) : m ^ n = (2 ^ n) ^ j := by
  rw [hm, ← pow_mul, ← pow_mul, mul_comm]

variable {X : Type} [Group X] [Finite X]

theorem b56_card_cases (h : B56QuasisimpleList X) (hq : CFSG.IsQuasisimple X)
    (h60 : 60 ∣ Nat.card X) :
    (∃ n, 1 ≤ n ∧ Nat.card X = 2 ^ n * (4 ^ n - 1)) ∨
      (∃ n, 1 ≤ n ∧ Nat.card X = 2 ^ (3 * n) * ((4 ^ n - 1) * (8 ^ n - 1))) ∨
      (∃ n, 2 ≤ n ∧ Nat.card X = 2 ^ (4 * n) * ((4 ^ n - 1) * (16 ^ n - 1))) ∨
      (∃ n, 1 ≤ n ∧ Nat.card X = 2 ^ (6 * n) * ((4 ^ n - 1) * (64 ^ n - 1))) ∨
      Nat.card X = 2 ^ 3 * 45 ∨ IsAlt 7 X ∨ Nat.card X = 2 ^ 3 * 135 ∨
      Nonempty (X ≃* ↥(StatedSL 4 (ZMod 2))) ∨ Nat.card X = 2 ^ 10 * 9765 := by
  have hpos : 0 < Nat.card X := Nat.card_pos
  rcases h with ⟨n, K, _, _, hK, ⟨e⟩⟩ | ⟨n, K, _, _, hK, ⟨e⟩⟩ | ⟨n, K, _, _, hK, ⟨e⟩⟩ |
    ⟨n, K, _, _, hK, ⟨e⟩⟩ | he6 | he | hhat | ⟨K, _, _, hK, ⟨e⟩⟩ | he | he5
  ·
    have hX : Nat.card X = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
      rw [Nat.card_congr e.toEquiv, card_statedSL_two1527d, hK]
    refine Or.inl ⟨n, Nat.pos_of_ne_zero fun h0 => ?_, ?_⟩
    · subst h0
      simp at hX
      omega
    · rw [hX, pow_eq_pow_pow n 4 2 (by norm_num)]
  ·
    have hX : Nat.card X = (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) := by
      rw [Nat.card_congr e.toEquiv, card_statedSL_three1527d, hK]
    refine Or.inr (Or.inl ⟨n, Nat.pos_of_ne_zero fun h0 => ?_, ?_⟩)
    · subst h0
      simp at hX
      omega
    · rw [hX, pow_two_mul n 3, pow_eq_pow_pow n 4 2 (by norm_num),
        pow_eq_pow_pow n 8 3 (by norm_num)]
  ·
    have hX : Nat.card X = (2 ^ n) ^ 4 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1)) := by
      rw [Nat.card_congr e.toEquiv,
        CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hK]
      have hI : Finset.Icc 1 2 = {1, 2} := by decide
      rw [hI, Finset.prod_pair (by norm_num)]
      norm_num
    refine Or.inr (Or.inr (Or.inl ⟨n, ?_, ?_⟩))
    swap
    · rw [hX, pow_two_mul n 4, pow_eq_pow_pow n 4 2 (by norm_num),
        pow_eq_pow_pow n 16 4 (by norm_num)]
    by_contra hn
    interval_cases n
    · simp at hX
      omega
    ·
      have : Group.IsPerfect X := hq.1
      exact Prop711.not_isPerfect_statedSp_two (K := K) (by rw [hK]; norm_num)
        (Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective)
  ·
    have hX : Nat.card X = (2 ^ n) ^ 6 * (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1)) := by
      rw [Nat.card_congr e.toEquiv, card_quasithinG2_1527d hK, hK]
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨n, Nat.pos_of_ne_zero fun h0 => ?_, ?_⟩)))
    · subst h0
      simp at hX
      omega
    · rw [hX, pow_two_mul n 6, pow_eq_pow_pow n 4 2 (by norm_num),
        pow_eq_pow_pow n 64 6 (by norm_num), mul_comm ((2 ^ n) ^ 6 - 1)]
  ·
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
    obtain ⟨e⟩ := he6
    rw [Nat.card_congr e.toEquiv, card_alternatingGroup1527d 6 (by norm_num)]
    simp [Nat.factorial]
  ·
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl he)))))
  ·
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))
    have hA : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
      rw [card_alternatingGroup1527d 6 (by norm_num)]
      simp [Nat.factorial]
    rw [card_of_isHat1527d hhat hA]
    norm_num
  ·
    exfalso
    have h2 : Nat.card K = 2 ^ 1 := by simpa using hK
    have hle : ⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆ ≤ CFSG.Open.quasithinG2 K :=
      Subgroup.commutator_le.mpr fun a ha b hb => by
        rw [commutatorElement_def]
        exact (CFSG.Open.quasithinG2 K).mul_mem ((CFSG.Open.quasithinG2 K).mul_mem
          ((CFSG.Open.quasithinG2 K).mul_mem ha hb) ((CFSG.Open.quasithinG2 K).inv_mem ha))
          ((CFSG.Open.quasithinG2 K).inv_mem hb)
    have h3 := Subgroup.card_dvd_of_le hle
    rw [card_quasithinG2_1527d h2, hK] at h3
    rw [Nat.card_congr e.toEquiv] at h60
    have h5 : 5 ∣ 2 ^ 1 * 2 ^ 1 * (2 ^ 1 * 2 ^ 1) * (2 ^ 1 * 2 ^ 1) *
        ((2 ^ 1 * 2 ^ 1 * (2 ^ 1 * 2 ^ 1) * (2 ^ 1 * 2 ^ 1) - 1) * (2 ^ 1 * 2 ^ 1 - 1)) := by
      have := (Dvd.intro_left 12 rfl : 5 ∣ 60).trans (h60.trans h3)
      simp only [pow_succ, pow_zero, one_mul] at this ⊢
      exact this
    norm_num at h5
  ·
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl he)))))))
  ·
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))))))
    obtain ⟨e⟩ := he5
    rw [Nat.card_congr e.toEquiv, card_statedSL_five_zmod1527d]
    norm_num

@[expose] def b56Chk (k : ℕ) (P : ℕ → Bool) : Bool :=
  !P (4 ^ k - 1) &&
    (k % 3 != 0 || !P ((4 ^ (k / 3) - 1) * (8 ^ (k / 3) - 1))) &&
    (k % 4 != 0 || decide (k / 4 < 2) || !P ((4 ^ (k / 4) - 1) * (16 ^ (k / 4) - 1))) &&
    (k % 6 != 0 || !P ((4 ^ (k / 6) - 1) * (64 ^ (k / 6) - 1))) &&
    (k != 3 || (!P 45 && !P 135)) && (k != 10 || !P 9765)

theorem b56_of_chk (h : B56QuasisimpleList X) (hq : CFSG.IsQuasisimple X)
    (h60 : 60 ∣ Nat.card X) {k d : ℕ} (hX : Nat.card X = 2 ^ k * d) (hd : Odd d)
    {P : ℕ → Bool} (hP : P d = true) (hchk : b56Chk k P = true) :
    (k = 3 ∧ d = 315 ∧ IsAlt 7 X) ∨ (k = 6 ∧ d = 315 ∧ Nonempty (X ≃* ↥(StatedSL 4 (ZMod 2)))) := by
  simp only [b56Chk, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at hchk
  obtain ⟨⟨⟨⟨⟨h1, h3⟩, h4⟩, h6⟩, h3'⟩, h10⟩ := hchk
  have h4o : Odd 4 → False := fun h => (Nat.not_even_iff_odd.mpr h) (by decide)
  have ho : ∀ m : ℕ, Even m → m ≠ 0 → ∀ n : ℕ, 1 ≤ n → Odd (m ^ n - 1) :=
    fun m hm hm0 n hn => odd_pow_sub_one hm hm0 (by omega)
  rcases b56_card_cases h hq h60 with ⟨n, hn, hc⟩ | ⟨n, hn, hc⟩ | ⟨n, hn, hc⟩ | ⟨n, hn, hc⟩ |
    hc | he | hc | he | hc
  · obtain ⟨rfl, rfl⟩ := eq_of_two_pow_mul_odd (ho 4 (by decide) (by norm_num) n hn) hd
      (hc.symm.trans hX)
    rw [hP] at h1
    exact absurd h1 (by decide)
  · obtain ⟨rfl, rfl⟩ := eq_of_two_pow_mul_odd
      ((ho 4 (by decide) (by norm_num) n hn).mul (ho 8 (by decide) (by norm_num) n hn)) hd
      (hc.symm.trans hX)
    rcases h3 with h3 | h3
    · exact absurd (by omega : 3 * n % 3 = 0) h3
    · rw [show 3 * n / 3 = n by omega, hP] at h3
      exact absurd h3 (by decide)
  · obtain ⟨rfl, rfl⟩ := eq_of_two_pow_mul_odd
      ((ho 4 (by decide) (by norm_num) n (by omega)).mul
        (ho 16 (by decide) (by norm_num) n (by omega))) hd (hc.symm.trans hX)
    rcases h4 with (h4 | h4) | h4
    · exact absurd (by omega : 4 * n % 4 = 0) h4
    · exact absurd h4 (by omega)
    · rw [show 4 * n / 4 = n by omega, hP] at h4
      exact absurd h4 (by decide)
  · obtain ⟨rfl, rfl⟩ := eq_of_two_pow_mul_odd
      ((ho 4 (by decide) (by norm_num) n hn).mul (ho 64 (by decide) (by norm_num) n hn)) hd
      (hc.symm.trans hX)
    rcases h6 with h6 | h6
    · exact absurd (by omega : 6 * n % 6 = 0) h6
    · rw [show 6 * n / 6 = n by omega, hP] at h6
      exact absurd h6 (by decide)
  · obtain ⟨rfl, rfl⟩ := eq_of_two_pow_mul_odd (by decide) hd (hc.symm.trans hX)
    rcases h3' with h3' | ⟨h45, -⟩
    · exact absurd rfl h3'
    · rw [hP] at h45
      exact absurd h45 (by decide)
  ·
    have hc : Nat.card X = 2 ^ 3 * 315 := by
      obtain ⟨e⟩ := he
      rw [Nat.card_congr e.toEquiv, card_alternatingGroup1527d 7 (by norm_num)]
      simp [Nat.factorial]
    obtain ⟨rfl, rfl⟩ := eq_of_two_pow_mul_odd (by decide) hd (hc.symm.trans hX)
    exact Or.inl ⟨rfl, rfl, he⟩
  · obtain ⟨rfl, rfl⟩ := eq_of_two_pow_mul_odd (by decide) hd (hc.symm.trans hX)
    rcases h3' with h3' | ⟨-, h135⟩
    · exact absurd rfl h3'
    · rw [hP] at h135
      exact absurd h135 (by decide)
  ·
    have hc : Nat.card X = 2 ^ 6 * 315 := by
      obtain ⟨e⟩ := he
      rw [Nat.card_congr e.toEquiv, card_statedSL_four_zmod1527d]
      norm_num
    obtain ⟨rfl, rfl⟩ := eq_of_two_pow_mul_odd (by decide) hd (hc.symm.trans hX)
    exact Or.inr ⟨rfl, rfl, he⟩
  · obtain ⟨rfl, rfl⟩ := eq_of_two_pow_mul_odd (by decide) hd (hc.symm.trans hX)
    rcases h10 with h10 | h10
    · exact absurd rfl h10
    · rw [hP] at h10
      exact absurd h10 (by decide)

end CFSG.Quasithin.H13.Ch9.FFB
