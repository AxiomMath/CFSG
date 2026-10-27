module

public import CFSG.Quasithin.Background.E2TwoLieQuot
public import CFSG.Quasithin.EmptyFaithful.R3c7Ord
public import CFSG.LieType.Ree.SuzukiOrder

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint

namespace E2

@[expose] def IsE22SmallType (X : Type) [Group X] : Prop :=
  (∃ p : ℕ, p.Prime ∧ (p % 8 = 1 ∨ p % 8 = 7) ∧ IsPSL 2 p 1 X) ∨
    (∃ p e : ℕ, p.Prime ∧ 3 < p ∧ (e = 1 ∨ e = 2) ∧ (p ^ e % 8 = 1 ∨ p ^ e % 8 = 7) ∧
      IsPSL 2 p e X) ∨
    (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ (IsPSU 3 p 1 X ∨ IsPSL 3 p 1 X)) ∨
    IsPSL 3 2 1 X ∨ IsSp4Prime 1 X

theorem padicValNat_and_lt_of_mul_odd {N g r a b : ℕ} (hg : Odd g) (hr : Odd r)
    (h : N * g = 2 ^ a * r) (hb : 2 ^ a * r < 2 ^ b) : padicValNat 2 N = a ∧ N < 2 ^ b :=
  ⟨R3c6.padicValNat_eq_of_mul_odd hg hr h,
    lt_of_le_of_lt (calc N ≤ N * g := Nat.le_mul_of_pos_right N hg.pos
      _ = 2 ^ a * r := h) hb⟩

theorem two_pow_mul_lt_two_pow {k c d r : ℕ} (hr : r < (2 ^ k) ^ d) :
    2 ^ (k * c) * r < 2 ^ (k * (c + d)) := by
  calc 2 ^ (k * c) * r < 2 ^ (k * c) * (2 ^ k) ^ d :=
        Nat.mul_lt_mul_of_pos_left hr (by positivity)
    _ = 2 ^ (k * (c + d)) := by rw [← pow_mul, ← pow_add, mul_add]

variable {X : Type} [Group X]

theorem card_shape_of_isE22LieType {k : ℕ} (hk : 2 ≤ k)
    (h : IsE22LieType k X) :
    Nat.card X = 2 ^ k * ((2 ^ k) ^ 2 - 1) ∨
      ∃ a b : ℕ, padicValNat 2 (Nat.card X) = a ∧ 6 ≤ a ∧ Nat.card X < 2 ^ b ∧
        3 * b ≤ 8 * a ∧ b + 2 ≤ 3 * a := by
  have hk0 : 0 < k := by omega
  have hQ : 4 ≤ 2 ^ k :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  rcases h with ⟨-, hL | hS | hU⟩ | hL3 | hSp
  ·
    left
    obtain ⟨-, -, -, hN⟩ := R3c6.psl2Data hL
    have hg : Nat.gcd 2 (2 ^ k - 1) = 1 :=
      Nat.Coprime.gcd_eq_one
        (Nat.coprime_two_left.mpr (CFSG.Timmesfeld.Orders.odd_two_pow_sub_one hk0))
    rwa [hg, mul_one] at hN
  ·
    right
    obtain ⟨-, a, ha, K, _, _, hka, hK, ⟨e⟩⟩ := hS
    have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hka]
    have hN : Nat.card X = (2 ^ k) ^ 2 * (2 ^ k - 1) * ((2 ^ k) ^ 2 + 1) := by
      rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK', ← hka]
    have hr : Odd ((2 ^ k - 1) * ((2 ^ k) ^ 2 + 1)) :=
      (CFSG.Timmesfeld.Orders.odd_two_pow_sub_one hk0).mul
        (CFSG.Timmesfeld.Orders.odd_pow_add_one hk0 (a := 2) (by norm_num))
    have hlt : (2 ^ k - 1) * ((2 ^ k) ^ 2 + 1) < (2 ^ k) ^ 3 := by
      have h1 : 1 ≤ 2 ^ k := by omega
      zify [h1]
      nlinarith
    obtain ⟨hν, hb⟩ := padicValNat_and_lt_of_mul_odd (N := Nat.card X) (g := 1) odd_one hr
      (a := k * 2) (b := k * (2 + 3)) (by rw [mul_one, hN, pow_mul]; ring)
      (two_pow_mul_lt_two_pow hlt)
    exact ⟨k * 2, k * (2 + 3), hν, by omega, hb, by omega, by omega⟩
  ·
    right
    obtain ⟨-, -, -, -, hN⟩ := R3c6.psu3Data hU
    have hg : Odd (Nat.gcd 3 (2 ^ k + 1)) := Odd.of_dvd_nat (by decide) (Nat.gcd_dvd_left _ _)
    have hr : Odd (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 3 + 1)) :=
      (CFSG.Timmesfeld.Orders.odd_pow_sub_one hk0 (a := 2) (by norm_num)).mul
        (CFSG.Timmesfeld.Orders.odd_pow_add_one hk0 (a := 3) (by norm_num))
    have hlt : ((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 3 + 1) < (2 ^ k) ^ 5 := by
      have h1 : 1 ≤ (2 ^ k) ^ 2 := Nat.one_le_pow _ _ (by positivity)
      have h23 : (2 ^ k) ^ 2 < (2 ^ k) ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
      zify [h1]
      nlinarith
    obtain ⟨hν, hb⟩ := padicValNat_and_lt_of_mul_odd hg hr (a := k * 3) (b := k * (3 + 5))
      (by rw [hN, pow_mul]) (two_pow_mul_lt_two_pow hlt)
    exact ⟨k * 3, k * (3 + 5), hν, by omega, hb, by omega, by omega⟩
  ·
    right
    obtain ⟨-, -, -, -, hN⟩ := R3c6.psl3Data hL3
    have hg : Odd (Nat.gcd 3 (2 ^ k - 1)) := Odd.of_dvd_nat (by decide) (Nat.gcd_dvd_left _ _)
    have hr : Odd (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 3 - 1)) :=
      (CFSG.Timmesfeld.Orders.odd_pow_sub_one hk0 (a := 2) (by norm_num)).mul
        (CFSG.Timmesfeld.Orders.odd_pow_sub_one hk0 (a := 3) (by norm_num))
    have hlt : ((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 3 - 1) < (2 ^ k) ^ 5 := by
      have e2 : (2 ^ k) ^ 2 - 1 < (2 ^ k) ^ 2 := Nat.sub_lt (by positivity) one_pos
      have e3 : (2 ^ k) ^ 3 - 1 < (2 ^ k) ^ 3 := Nat.sub_lt (by positivity) one_pos
      calc ((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 3 - 1) < (2 ^ k) ^ 2 * (2 ^ k) ^ 3 :=
            Nat.mul_lt_mul'' e2 e3
        _ = (2 ^ k) ^ 5 := by ring
    obtain ⟨hν, hb⟩ := padicValNat_and_lt_of_mul_odd hg hr (a := k * 3) (b := k * (3 + 5))
      (by rw [hN, pow_mul]) (two_pow_mul_lt_two_pow hlt)
    exact ⟨k * 3, k * (3 + 5), hν, by omega, hb, by omega, by omega⟩
  ·
    right
    have hN : Nat.card X = CFSG.Open.ordBC 2 (2 ^ k) :=
      (CFSG.Timmesfeld.card_statedClassicalModel_two hSp).2.2.1 rfl
    rw [R3c6.ordBC_two_eq (by omega)] at hN
    have hr : Odd (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 4 - 1)) :=
      (CFSG.Timmesfeld.Orders.odd_pow_sub_one hk0 (a := 2) (by norm_num)).mul
        (CFSG.Timmesfeld.Orders.odd_pow_sub_one hk0 (a := 4) (by norm_num))
    have hlt : ((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 4 - 1) < (2 ^ k) ^ 6 := by
      have e2 : (2 ^ k) ^ 2 - 1 < (2 ^ k) ^ 2 := Nat.sub_lt (by positivity) one_pos
      have e4 : (2 ^ k) ^ 4 - 1 < (2 ^ k) ^ 4 := Nat.sub_lt (by positivity) one_pos
      calc ((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 4 - 1) < (2 ^ k) ^ 2 * (2 ^ k) ^ 4 :=
            Nat.mul_lt_mul'' e2 e4
        _ = (2 ^ k) ^ 6 := by ring
    obtain ⟨hν, hb⟩ := padicValNat_and_lt_of_mul_odd (N := Nat.card X) (g := 1) odd_one hr
      (a := k * 4) (b := k * (4 + 6)) (by rw [mul_one, hN]) (two_pow_mul_lt_two_pow hlt)
    exact ⟨k * 4, k * (4 + 6), hν, by omega, hb, by omega, by omega⟩

theorem ordClass_of_card_shape {k N : ℕ} (hk : 2 ≤ k)
    (h : N = 2 ^ k * ((2 ^ k) ^ 2 - 1) ∨
      ∃ a b : ℕ, padicValNat 2 N = a ∧ 6 ≤ a ∧ N < 2 ^ b ∧ 3 * b ≤ 8 * a ∧ b + 2 ≤ 3 * a) :
    R3c7.OrdClass N := by
  rcases h with hL | ⟨a, b, ha, -, hb, h1, h2⟩
  · exact R3c7.OrdClass.l2two hk hL
  · exact R3c7.OrdClass.big2 ha hb h1 h2

theorem false_of_card_shape_of_l2p {k N p : ℕ} (hk : 2 ≤ k)
    (h : N = 2 ^ k * ((2 ^ k) ^ 2 - 1) ∨
      ∃ a b : ℕ, padicValNat 2 N = a ∧ 6 ≤ a ∧ N < 2 ^ b ∧ 3 * b ≤ 8 * a ∧ b + 2 ≤ 3 * a)
    (hp : p.Prime) (hp8 : p % 8 = 1 ∨ p % 8 = 7) (hN : N * 2 = p * (p ^ 2 - 1)) : False := by
  rcases h with hL | ⟨a, b, ha, -, hb, -, h2⟩
  · exact R3c7.false_of_l2two_l2p hk hL hp hp8 hN
  · have hp7 : 7 ≤ p := by
      have := hp.two_le
      omega
    have hodd : Odd p := hp.odd_of_ne_two (by omega)
    have h3 := R3c7.two_pow_three_le_of_l2p hodd hp7 hN
    rw [ha] at h3
    have h4 : 2 ^ (b + 2) ≤ 2 ^ (3 * a) := Nat.pow_le_pow_right (by norm_num) h2
    have h5 : 4 * N < 2 ^ (b + 2) := by rw [pow_add]; omega
    omega

theorem false_of_card_shape_of_small {k N : ℕ} (hk : 2 ≤ k)
    (h : N = 2 ^ k * ((2 ^ k) ^ 2 - 1) ∨
      ∃ a b : ℕ, padicValNat 2 N = a ∧ 6 ≤ a ∧ N < 2 ^ b ∧ 3 * b ≤ 8 * a ∧ b + 2 ≤ 3 * a)
    (hN : N = 168 ∨ N = 360 ∨ N = 5616 ∨ N = 6048) : False := by
  rcases h with hL | ⟨a, b, ha, ha6, -⟩
  · have hk5 : k ≤ 5 := by
      by_contra hlt
      have h6 : 2 ^ 6 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h7 : 2 ^ 6 * ((2 ^ 6) ^ 2 - 1) ≤ 2 ^ k * ((2 ^ k) ^ 2 - 1) :=
        Nat.mul_le_mul h6 (Nat.sub_le_sub_right (Nat.pow_le_pow_left h6 2) 1)
      omega
    rcases hN with rfl | rfl | rfl | rfl <;> interval_cases k <;> norm_num at hL
  · have hν : padicValNat 2 N ≤ 5 := by
      rcases hN with rfl | rfl | rfl | rfl
      · have := R3c6.padicValNat_eq_of_mul_odd (N := 168) (g := 1) (r := 21) (a := 3) odd_one
          (by decide) (by norm_num)
        omega
      · have := R3c6.padicValNat_eq_of_mul_odd (N := 360) (g := 1) (r := 45) (a := 3) odd_one
          (by decide) (by norm_num)
        omega
      · have := R3c6.padicValNat_eq_of_mul_odd (N := 5616) (g := 1) (r := 351) (a := 4) odd_one
          (by decide) (by norm_num)
        omega
      · have := R3c6.padicValNat_eq_of_mul_odd (N := 6048) (g := 1) (r := 189) (a := 5) odd_one
          (by decide) (by norm_num)
        omega
    omega

theorem not_isE22SmallType_of_isE22LieType {k : ℕ} (hk : 2 ≤ k)
    (h : IsE22LieType k X) : ¬ IsE22SmallType X := by
  have hshape := card_shape_of_isE22LieType hk h
  have hcls := ordClass_of_card_shape hk hshape
  have hl2 : ∀ p : ℕ, p.Prime → (p % 8 = 1 ∨ p % 8 = 7) → IsPSL 2 p 1 X → False := by
    intro p hp hp8 hX
    obtain ⟨-, -, -, hN⟩ := R3c6.psl2Data hX
    have hodd : Odd p := hp.odd_of_ne_two (by omega)
    have hg : Nat.gcd 2 (p ^ 1 - 1) = 2 := by
      apply Nat.gcd_eq_left
      rw [pow_one]
      exact even_iff_two_dvd.mp (Nat.Odd.sub_odd hodd odd_one)
    rw [hg, pow_one] at hN
    exact false_of_card_shape_of_l2p hk hshape hp hp8 hN
  rintro (⟨p, hp, hp8, hX⟩ | ⟨p, e, hp, hp3, he, hpe8, hX⟩ | ⟨p, hp, hp2, hX | hX⟩ | hX | hX)
  · exact hl2 p hp hp8 hX
  · rcases he with rfl | rfl
    · rw [pow_one] at hpe8
      exact hl2 p hp hpe8 hX
    · obtain ⟨-, -, -, hN⟩ := R3c6.psl2Data hX
      have hodd : Odd p := hp.odd_of_ne_two (by omega)
      have hg : Nat.gcd 2 (p ^ 2 - 1) = 2 := by
        apply Nat.gcd_eq_left
        exact even_iff_two_dvd.mp (Nat.Odd.sub_odd (hodd.pow) odd_one)
      rw [hg] at hN
      have hN' : Nat.card X * 2 = p ^ 2 * (p ^ 4 - 1) := by
        rw [hN, ← pow_mul]
      have h4 : p ≠ 4 := by
        rintro rfl
        norm_num at hp
      have hp5 : 5 ≤ p := by omega
      exact R3c7.OrdClass.false_of_l2sq hcls hp hp5 hN'
  · by_cases hp5 : 5 ≤ p
    · obtain ⟨-, -, -, -, hN⟩ := R3c6.psu3Data hX
      simp only [pow_one] at hN
      exact R3c7.OrdClass.false_of_oddLike hcls (R3c7.oddLike_of_su3 hp hp5 rfl hN)
    · have hp3 : p = 3 := by
        have h2 := hp.two_le
        have h4 : p ≠ 4 := by
          rintro rfl
          norm_num at hp
        omega
      subst hp3
      obtain ⟨-, -, -, -, hN⟩ := R3c6.psu3Data hX
      have hN' : Nat.card X = 6048 := by simpa using hN
      exact false_of_card_shape_of_small hk hshape (by omega)
  · by_cases hp5 : 5 ≤ p
    · obtain ⟨-, -, -, -, hN⟩ := R3c6.psl3Data hX
      simp only [pow_one] at hN
      exact R3c7.OrdClass.false_of_oddLike hcls (R3c7.oddLike_of_sl3 hp hp5 rfl hN)
    · have hp3 : p = 3 := by
        have h2 := hp.two_le
        have h4 : p ≠ 4 := by
          rintro rfl
          norm_num at hp
        omega
      subst hp3
      obtain ⟨-, -, -, -, hN⟩ := R3c6.psl3Data hX
      have hN' : Nat.card X = 5616 := by simpa using hN
      exact false_of_card_shape_of_small hk hshape (by omega)
  · obtain ⟨-, -, -, -, hN⟩ := R3c6.psl3Data hX
    have hN' : Nat.card X = 168 := by norm_num at hN; exact hN
    exact false_of_card_shape_of_small hk hshape (by omega)
  · simp only [IsSp4Prime, ↓reduceIte] at hX
    obtain ⟨e⟩ := hX
    have hN : Nat.card X = 360 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
    exact false_of_card_shape_of_small hk hshape (by omega)

end E2

end CFSG.Quasithin
