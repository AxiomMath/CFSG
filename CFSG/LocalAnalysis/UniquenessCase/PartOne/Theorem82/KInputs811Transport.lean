module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811Centre


public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open Subgroup

variable {Y : Type} [Group Y]

theorem qPlusPi_eq_qMinusPi_add_two_or {r f : ℕ} (hq : 1 ≤ r ^ f) :
    qPlusPi r f = qMinusPi r f + 2 ∨ qMinusPi r f = qPlusPi r f + 2 := by
  unfold qPlusPi qMinusPi
  split_ifs <;> omega

theorem prime_and_one_le_of_isLie811 {fam : LieFam811} {r f : ℕ} (h : IsLie811 Y fam r f) :
    r.Prime ∧ 1 ≤ f := by
  obtain ⟨-, -, hfam⟩ := h
  rcases fam with _ | _ | _ | _ | _ | _
  · obtain ⟨hr, -, hm⟩ := hfam
    exact ⟨hr, hm.admissible.2.1⟩
  · obtain ⟨hr, -, -, hm⟩ := hfam
    exact ⟨hr, hm.admissible.2.1⟩
  · obtain ⟨hr, -, hm⟩ := hfam
    exact ⟨hr, hm.admissible.2.1⟩
  · obtain ⟨hr, -, ⟨-, hm⟩ | ⟨-, hm⟩⟩ := hfam <;> exact ⟨hr, hm.admissible.2.1⟩
  · obtain ⟨hr, ⟨-, hm⟩ | ⟨-, hm⟩⟩ := hfam <;> exact ⟨hr, hm.admissible.2.1⟩
  · obtain ⟨hr, ⟨-, hm⟩ | ⟨-, hm⟩⟩ := hfam <;> exact ⟨hr, hm.admissible.2.1⟩

theorem pow_mod_three_cases_of_isLie811 {fam : LieFam811} {r f : ℕ} (h : IsLie811 Y fam r f)
    (hfam : fam = .l4 ∨ fam = .l6 ∨ fam = .l7) : r ^ f % 3 = 1 ∨ r ^ f % 3 = 2 := by
  obtain ⟨-, -, hf⟩ := h
  rcases hfam with rfl | rfl | rfl
  · obtain ⟨-, -, ⟨h1, -⟩ | ⟨h2, -⟩⟩ := hf
    exacts [Or.inl h1, Or.inr h2]
  · obtain ⟨-, ⟨h2, -⟩ | ⟨h1, -⟩⟩ := hf
    exacts [Or.inr h2, Or.inl h1]
  · obtain ⟨-, ⟨h2, -⟩ | ⟨h1, -⟩⟩ := hf
    exacts [Or.inr h2, Or.inl h1]

section Centre

theorem card_center_eq_one_or_seven_of_isLie811 {fam : LieFam811} {r f : ℕ}
    (h : IsLie811 Y fam r f) :
    Nat.card (center Y) = 1 ∨ (fam = .l7 ∧ Nat.card (center Y) = 7 ∧ 7 ∣ qPlusPi r f) := by
  rcases eq_or_ne fam .l7 with rfl | hne
  · have hd := card_center_dvd_of_isLie811_l7 h
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).1
      (hd.trans (Nat.gcd_dvd_left 7 (qPlusPi r f))) with h1 | h7
    · exact Or.inl h1
    · exact Or.inr ⟨rfl, h7, (Nat.dvd_gcd_iff.1 (h7 ▸ hd)).2⟩
  · rw [center_eq_bot_of_isLie811 h hne, Subgroup.card_bot]
    exact Or.inl rfl

theorem card_center_eq_one_of_isLie811_of_ne_l7 {fam : LieFam811} {r f : ℕ}
    (h : IsLie811 Y fam r f) (hfam : fam ≠ .l7) : Nat.card (center Y) = 1 := by
  rw [center_eq_bot_of_isLie811 h hfam, Subgroup.card_bot]

theorem not_dvd_card_center_or_eq_of_isLie811 {fam : LieFam811} {r f : ℕ}
    (h : IsLie811 Y fam r f) {p : ℕ} (hp : p.Prime) :
    ¬ p ∣ Nat.card (center Y) ∨ Nat.card (center Y) = p := by
  rcases card_center_eq_one_or_seven_of_isLie811 h with h1 | ⟨-, h7, -⟩
  · exact Or.inl fun hd => hp.one_lt.ne' (Nat.dvd_one.1 (h1 ▸ hd))
  · by_cases hp7 : p ∣ 7
    · exact Or.inr (h7.trans ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 hp7).symm)
    · exact Or.inl fun hd => hp7 (h7 ▸ hd)

theorem not_dvd_card_center_of_isLie811_of_dvd_qMinusPi {fam : LieFam811} {r f : ℕ}
    (h : IsLie811 Y fam r f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hd : p ∣ qMinusPi r f) :
    ¬ p ∣ Nat.card (center Y) := by
  rcases card_center_eq_one_or_seven_of_isLie811 h with h1 | ⟨-, h7, h7q⟩
  · exact fun hd' => hp.one_lt.ne' (Nat.dvd_one.1 (h1 ▸ hd'))
  · intro hd'
    have hp7 : p = 7 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 (h7 ▸ hd')
    subst hp7
    have hq : 1 ≤ r ^ f := Nat.one_le_pow _ _ (prime_and_one_le_of_isLie811 h).1.pos
    rcases qPlusPi_eq_qMinusPi_add_two_or hq with h2 | h2 <;> omega

theorem not_dvd_card_center_of_isLie811_char {fam : LieFam811} {r f : ℕ}
    (h : IsLie811 Y fam r f) (hr5 : 5 ≤ r) : ¬ r ∣ Nat.card (center Y) := by
  obtain ⟨hr, hf⟩ := prime_and_one_le_of_isLie811 h
  rcases card_center_eq_one_or_seven_of_isLie811 h with h1 | ⟨-, h7, h7q⟩
  · exact fun hd' => hr.one_lt.ne' (Nat.dvd_one.1 (h1 ▸ hd'))
  · intro hd'
    have hr7 : r = 7 := (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).1 (h7 ▸ hd')
    subst hr7
    have h7f : 7 ∣ 7 ^ f := dvd_pow_self 7 (by omega)
    have h1 : 1 ≤ 7 ^ f := Nat.one_le_pow _ _ (by norm_num)
    unfold qPlusPi at h7q
    split_ifs at h7q <;> omega

end Centre

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
