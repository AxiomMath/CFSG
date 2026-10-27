module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem25PerfInputs
public import CFSG.Timmesfeld.Orders.Exceptional
public import CFSG.LieType.Ree.LargeReeModelSchreier
public import CFSG.RankThree.SteinbergR3ELargeReeOrder

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint

namespace ExcSmall

variable {X : Type} [Group X]

theorem not_isE22SmallType_of_card_shape {k : ℕ} (hk : 2 ≤ k)
    (hshape : Nat.card X = 2 ^ k * ((2 ^ k) ^ 2 - 1) ∨
      ∃ a b : ℕ, padicValNat 2 (Nat.card X) = a ∧ 6 ≤ a ∧ Nat.card X < 2 ^ b ∧
        3 * b ≤ 8 * a ∧ b + 2 ≤ 3 * a) : ¬ E2.IsE22SmallType X := by
  have hcls := E2.ordClass_of_card_shape hk hshape
  have hl2 : ∀ p : ℕ, p.Prime → (p % 8 = 1 ∨ p % 8 = 7) → IsPSL 2 p 1 X → False := by
    intro p hp hp8 hX
    obtain ⟨-, -, -, hN⟩ := R3c6.psl2Data hX
    have hodd : Odd p := hp.odd_of_ne_two (by omega)
    have hg : Nat.gcd 2 (p ^ 1 - 1) = 2 := by
      apply Nat.gcd_eq_left
      rw [pow_one]
      exact even_iff_two_dvd.mp (Nat.Odd.sub_odd hodd odd_one)
    rw [hg, pow_one] at hN
    exact E2.false_of_card_shape_of_l2p hk hshape hp hp8 hN
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
      exact E2.false_of_card_shape_of_small hk hshape (by omega)
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
      exact E2.false_of_card_shape_of_small hk hshape (by omega)
  · obtain ⟨-, -, -, -, hN⟩ := R3c6.psl3Data hX
    have hN' : Nat.card X = 168 := by norm_num at hN; exact hN
    exact E2.false_of_card_shape_of_small hk hshape (by omega)
  · simp only [E2.IsSp4Prime, ↓reduceIte] at hX
    obtain ⟨e⟩ := hX
    have hN : Nat.card X = 360 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
    exact E2.false_of_card_shape_of_small hk hshape (by omega)

omit [Group X] in
theorem card_shape_of_mul_odd {k c d r : ℕ} (hk : 1 ≤ k) (hr : Odd r)
    (hN : Nat.card X = 2 ^ (k * c) * r) (hlt : r < (2 ^ k) ^ d) (hc : 6 ≤ c)
    (h1 : 3 * (c + d) ≤ 8 * c) (h2 : c + d + 2 ≤ 3 * c) :
    ∃ a b : ℕ, padicValNat 2 (Nat.card X) = a ∧ 6 ≤ a ∧ Nat.card X < 2 ^ b ∧
      3 * b ≤ 8 * a ∧ b + 2 ≤ 3 * a := by
  obtain ⟨hν, hb⟩ := E2.padicValNat_and_lt_of_mul_odd (N := Nat.card X) (g := 1) odd_one hr
    (a := k * c) (b := k * (c + d)) (by rw [mul_one, hN]) (E2.two_pow_mul_lt_two_pow hlt)
  refine ⟨k * c, k * (c + d), hν, ?_, hb, ?_, ?_⟩
  · calc 6 ≤ c := hc
      _ = 1 * c := (one_mul c).symm
      _ ≤ k * c := Nat.mul_le_mul_right c hk
  · calc 3 * (k * (c + d)) = k * (3 * (c + d)) := by ring
      _ ≤ k * (8 * c) := Nat.mul_le_mul_left k h1
      _ = 8 * (k * c) := by ring
  · have h3 : k * (c + d + 2) ≤ k * (3 * c) := Nat.mul_le_mul_left k h2
    have h4 : 2 ≤ 2 * k := by omega
    calc k * (c + d) + 2 ≤ k * (c + d) + 2 * k := by omega
      _ = k * (c + d + 2) := by ring
      _ ≤ k * (3 * c) := h3
      _ = 3 * (k * c) := by ring

theorem odd_pow_sub_one' {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) : Odd ((2 ^ k) ^ n - 1) := by
  rw [← pow_mul]
  exact CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by positivity)

theorem odd_pow_add_one' {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) : Odd ((2 ^ k) ^ n + 1) := by
  rw [← pow_mul]
  exact (Nat.even_pow.mpr ⟨even_two, by positivity⟩).add_one

theorem pow_sub_one_lt (k n : ℕ) : (2 ^ k) ^ n - 1 < (2 ^ k) ^ n :=
  Nat.sub_lt (by positivity) one_pos

theorem pow_add_one_le {k : ℕ} (hk : 1 ≤ k) (n : ℕ) : (2 ^ k) ^ n + 1 ≤ (2 ^ k) ^ (n + 1) := by
  have h2 : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have h1 : 1 ≤ (2 ^ k) ^ n := Nat.one_le_pow _ _ (by positivity)
  rw [pow_succ]
  nlinarith

theorem card_shape_g2 {X : Type} [Group X] {k : ℕ} (hk : 1 ≤ k)
    (hN : Nat.card X = ordG2 (2 ^ k)) :
    ∃ a b : ℕ, padicValNat 2 (Nat.card X) = a ∧ 6 ≤ a ∧ Nat.card X < 2 ^ b ∧
      3 * b ≤ 8 * a ∧ b + 2 ≤ 3 * a := by
  have e6 : (2 ^ k) ^ 6 = 2 ^ (k * 6) := (pow_mul 2 k 6).symm
  refine card_shape_of_mul_odd (c := 6) (d := 10) (r := ((2 ^ k) ^ 6 - 1) * ((2 ^ k) ^ 2 - 1)) hk
    ((odd_pow_sub_one' (n := 6) hk (by norm_num)).mul (odd_pow_sub_one' (n := 2) hk (by norm_num)))
    (by rw [hN, ordG2, e6, mul_assoc]) ?_ le_rfl (by norm_num) (by norm_num)
  calc ((2 ^ k) ^ 6 - 1) * ((2 ^ k) ^ 2 - 1) < (2 ^ k) ^ 6 * (2 ^ k) ^ 2 :=
        Nat.mul_lt_mul'' (pow_sub_one_lt k 6) (pow_sub_one_lt k 2)
    _ = (2 ^ k) ^ 8 := by ring
    _ ≤ (2 ^ k) ^ 10 := Nat.pow_le_pow_right (by positivity) (by norm_num)

theorem card_shape_d4 {X : Type} [Group X] {k : ℕ} (hk : 1 ≤ k)
    (hN : Nat.card X = ordTrialityD4 (2 ^ k)) :
    ∃ a b : ℕ, padicValNat 2 (Nat.card X) = a ∧ 6 ≤ a ∧ Nat.card X < 2 ^ b ∧
      3 * b ≤ 8 * a ∧ b + 2 ≤ 3 * a := by
  have hq : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hodd : Odd ((2 ^ k) ^ 8 + (2 ^ k) ^ 4 + 1) := by
    have h8 : Even ((2 ^ k) ^ 8) := by
      rw [← pow_mul]
      exact Nat.even_pow.mpr ⟨even_two, by positivity⟩
    have h4 : Even ((2 ^ k) ^ 4) := by
      rw [← pow_mul]
      exact Nat.even_pow.mpr ⟨even_two, by positivity⟩
    exact (h8.add h4).add_one
  have hA : (2 ^ k) ^ 8 + (2 ^ k) ^ 4 + 1 ≤ (2 ^ k) ^ 9 := by
    have hQ : 2 ≤ (2 ^ k) ^ 4 :=
      le_trans hq (Nat.le_self_pow (by norm_num) _)
    have e8 : (2 ^ k) ^ 8 = (2 ^ k) ^ 4 * (2 ^ k) ^ 4 := by ring
    have e9 : (2 ^ k) ^ 9 = 2 ^ k * ((2 ^ k) ^ 4 * (2 ^ k) ^ 4) := by ring
    have h1 : (2 ^ k) ^ 4 + 1 ≤ (2 ^ k) ^ 4 * (2 ^ k) ^ 4 := by nlinarith
    have h2 : 2 * ((2 ^ k) ^ 4 * (2 ^ k) ^ 4) ≤ 2 ^ k * ((2 ^ k) ^ 4 * (2 ^ k) ^ 4) :=
      Nat.mul_le_mul_right _ hq
    rw [e8, e9]
    omega
  have e12 : (2 ^ k) ^ 12 = 2 ^ (k * 12) := (pow_mul 2 k 12).symm
  refine card_shape_of_mul_odd (c := 12) (d := 20)
    (r := ((2 ^ k) ^ 8 + (2 ^ k) ^ 4 + 1) * ((2 ^ k) ^ 6 - 1) * ((2 ^ k) ^ 2 - 1)) hk
    ((hodd.mul (odd_pow_sub_one' (n := 6) hk (by norm_num))).mul
      (odd_pow_sub_one' (n := 2) hk (by norm_num)))
    (by rw [hN, ordTrialityD4, e12]; ring) ?_ (by norm_num) (by norm_num) (by norm_num)
  calc ((2 ^ k) ^ 8 + (2 ^ k) ^ 4 + 1) * ((2 ^ k) ^ 6 - 1) * ((2 ^ k) ^ 2 - 1) <
        (2 ^ k) ^ 9 * (2 ^ k) ^ 6 * (2 ^ k) ^ 2 :=
        Nat.mul_lt_mul'' (Nat.mul_lt_mul_of_le_of_lt hA (pow_sub_one_lt k 6) (by positivity))
          (pow_sub_one_lt k 2)
    _ = (2 ^ k) ^ 17 := by ring
    _ ≤ (2 ^ k) ^ 20 := Nat.pow_le_pow_right (by positivity) (by norm_num)

theorem card_shape_f4 {X : Type} [Group X] {k : ℕ} (hk : 1 ≤ k)
    (hN : Nat.card X = ordTwistedF4 (2 ^ k)) :
    ∃ a b : ℕ, padicValNat 2 (Nat.card X) = a ∧ 6 ≤ a ∧ Nat.card X < 2 ^ b ∧
      3 * b ≤ 8 * a ∧ b + 2 ≤ 3 * a := by
  have hq1 : (2 ^ k) - 1 < 2 ^ k := Nat.sub_lt (by positivity) one_pos
  have hodd1 : Odd (2 ^ k - 1) := CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by omega)
  have e12 : (2 ^ k) ^ 12 = 2 ^ (k * 12) := (pow_mul 2 k 12).symm
  refine card_shape_of_mul_odd (c := 12) (d := 20)
    (r := ((2 ^ k) ^ 6 + 1) * ((2 ^ k) ^ 4 - 1) * ((2 ^ k) ^ 3 + 1) * (2 ^ k - 1)) hk
    ((((odd_pow_add_one' (n := 6) hk (by norm_num)).mul
      (odd_pow_sub_one' (n := 4) hk (by norm_num))).mul
      (odd_pow_add_one' (n := 3) hk (by norm_num))).mul hodd1)
    (by rw [hN, ordTwistedF4, e12]; ring) ?_ (by norm_num) (by norm_num) (by norm_num)
  calc ((2 ^ k) ^ 6 + 1) * ((2 ^ k) ^ 4 - 1) * ((2 ^ k) ^ 3 + 1) * (2 ^ k - 1) <
        (2 ^ k) ^ 7 * (2 ^ k) ^ 4 * (2 ^ k) ^ 4 * 2 ^ k :=
        Nat.mul_lt_mul_of_le_of_lt (Nat.mul_le_mul (Nat.mul_le_mul (pow_add_one_le hk 6)
          (pow_sub_one_lt k 4).le) (pow_add_one_le hk 3)) hq1 (by positivity)
    _ = (2 ^ k) ^ 16 := by ring
    _ ≤ (2 ^ k) ^ 20 := Nat.pow_le_pow_right (by positivity) (by norm_num)

theorem card_of_reeTitsModel_twistedF4
    {G : Type} [Group G] {f : ℕ} (h : ReeTitsModel G .twistedF4 2 f) :
    Nat.card G = ordTwistedF4 (2 ^ f) := by
  have hS := CFSG.LieType.Ree.ReeTag.large_Ree_model_Schreier G 2 f h
  obtain ⟨-, a, hfa, hmodel⟩ := h
  subst hfa
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmodel
  have : Fintype K := Fintype.ofFinite K
  have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := charP_of_card_eq_prime_pow
    (f := 2 * a + 1) (by
      rw [← Nat.card_eq_fintype_card, hK]
      rfl)
  obtain ⟨E⟩ := hS.2.2.2.2.2 a K rfl hK ⟨e⟩
  have hord :=
    (CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion a K
      hK).1
  rw [Nat.card_congr E.toEquiv, hord, ordTwistedF4]
  set q := 2 ^ (2 * a + 1) with hq
  have h1 : 1 ≤ q := Nat.one_le_two_pow
  have h2 : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  have h3 : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h4 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ (by omega)
  zify [h1, h2, h3, h4]
  ring

end ExcSmall

open ExcSmall

theorem excRank2NotSmallFact_holds :
    ExcRank2NotSmallFact := by
  intro S _ ⟨k, hk, h⟩
  apply not_isE22SmallType_of_card_shape hk
  right
  rcases h with h | h | h
  · exact card_shape_g2 (by omega) (CFSG.Timmesfeld.card_chevalleyExceptionalModel_two h)
  · exact card_shape_d4 (by omega) (CFSG.Timmesfeld.card_chevalleyExceptionalModel_two h)
  · exact card_shape_f4 (by omega) (card_of_reeTitsModel_twistedF4 h)

end CFSG.Quasithin.H13
