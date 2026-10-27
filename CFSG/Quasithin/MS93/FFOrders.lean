module

public import CFSG.Quasithin.MS93.FFStatement
public import CFSG.Quasithin.H13.VolIA38Orders
public import CFSG.Quasithin.H13.L1332Inputs
public import CFSG.RankThree.PartOne.S12K.OrdRigid
public import CFSG.Quasithin.Vol2.Ch11L2Q5cF4Ord
import all CFSG.Timmesfeld.Orders.Distinct
public import CFSG.Quasithin.H13.ExcludedOrders
public import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.Timmesfeld.Orders.Exceptional

public section

namespace CFSG.Quasithin.MS93

open CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Orders CFSG.Quasithin.H13.VolI

private theorem not_dvd_of_scaled {a b c x y : ℕ} (ha : 0 < a) (hx : x = a * b)
    (hy : y = a * c) (h : ¬ b ∣ c) : ¬ x ∣ y := by
  rintro hd
  subst hx hy
  exact h (Nat.dvd_of_mul_dvd_mul_left ha hd)

theorem ordA_two_ne_ordTrialityD4 {n e : ℕ} (hn : 1 ≤ n) (he : 1 ≤ e) :
    ordA 2 (2 ^ n) ≠ ordTrialityD4 (2 ^ e) := by
  intro h
  have P1 := profile_ordA (n := 2) (f := n) (by norm_num) hn
  rw [h] at P1
  obtain ⟨hN, hZ⟩ := Profile.transfer P1 (profile_ordTrialityD4 he)
  have hn4 : n = 4 * e := by norm_num at hN; omega
  have hz : zA 2 n (8 * e) := ⟨2, by simp, ⟨1, by rw [hn4]; ring⟩⟩
  rcases (hZ (8 * e) (by omega) (by omega)).1 hz with ⟨h12, -⟩ | h6 | h2
  · exact not_dvd_of_scaled (a := 4 * e) (b := 2) (c := 3) (by omega) (by ring) (by ring)
      (by decide) h12
  · exact not_dvd_of_scaled (a := 2 * e) (b := 4) (c := 3) (by omega) (by ring) (by ring)
      (by decide) h6
  · exact not_dvd_of_scaled (a := 2 * e) (b := 4) (c := 1) (by omega) (by ring) (by ring)
      (by decide) h2

theorem ordA_two_ne_ordTwistedF4 {n f : ℕ} (hn : 1 ≤ n) (hf : 1 ≤ f) :
    ordA 2 (2 ^ n) ≠ ordTwistedF4 (2 ^ f) := by
  intro h
  have P1 := profile_ordA (n := 2) (f := n) (by norm_num) hn
  rw [h] at P1
  obtain ⟨hN, hZ⟩ := Profile.transfer P1 (profile_ordTwistedF4 hf)
  have hn4 : n = 4 * f := by norm_num at hN; omega
  have hz : zA 2 n (8 * f) := ⟨2, by simp, ⟨1, by rw [hn4]; ring⟩⟩
  rcases (hZ (8 * f) (by omega) (by omega)).1 hz with ⟨h12, -⟩ | h4 | ⟨h6, -⟩ | h1
  · exact not_dvd_of_scaled (a := 4 * f) (b := 2) (c := 3) (by omega) (by ring) (by ring)
      (by decide) h12
  · exact not_dvd_of_scaled (a := 4 * f) (b := 2) (c := 1) (by omega) (by ring) (by ring)
      (by decide) h4
  · exact not_dvd_of_scaled (a := 2 * f) (b := 4) (c := 3) (by omega) (by ring) (by ring)
      (by decide) h6
  · exact not_dvd_of_scaled (a := f) (b := 8) (c := 1) (by omega) (by ring) (by ring)
      (by decide) h1

theorem ordG2_ne_ordTrialityD4 {n e : ℕ} (hn : 1 ≤ n) (he : 1 ≤ e) :
    ordG2 (2 ^ n) ≠ ordTrialityD4 (2 ^ e) := by
  intro h
  have P1 := profile_ordG2 hn
  rw [h] at P1
  obtain ⟨hN, hZ⟩ := Profile.transfer P1 (profile_ordTrialityD4 he)
  have hn2 : n = 2 * e := by omega
  have hz : zG2 n (4 * e) := ⟨2, by simp, ⟨1, by rw [hn2]; ring⟩⟩
  rcases (hZ (4 * e) (by omega) (by omega)).1 hz with ⟨-, h4⟩ | h6 | h2
  · exact h4 (by rw [mul_comm])
  · exact not_dvd_of_scaled (a := 2 * e) (b := 2) (c := 3) (by omega) (by ring) (by ring)
      (by decide) h6
  · exact not_dvd_of_scaled (a := 2 * e) (b := 2) (c := 1) (by omega) (by ring) (by ring)
      (by decide) h2

@[expose] def ExcludedOrder (m : ℕ) : Prop :=
  (∃ e, 1 ≤ e ∧ m = ordTrialityD4 (2 ^ e)) ∨
    (∃ k, 1 ≤ k ∧ m = ordTwistedF4 (2 ^ (2 * k + 1))) ∨ m = ordTits ∨
    (∃ e, 1 ≤ e ∧ m = ordTwistedA 3 (2 ^ e)) ∨ (∃ e, 1 ≤ e ∧ m = ordTwistedA 4 (2 ^ e))

theorem not_excludedOrder_of_two_part {m N : ℕ} (hm : ∃ r, Odd r ∧ m = 2 ^ N * r)
    (h12 : ∀ e, N ≠ e * 12) (h11 : N ≠ 11) (h6 : ∀ e, N ≠ e * 6) (h10 : ∀ e, N ≠ e * 10) :
    ¬ ExcludedOrder m := by
  rintro (⟨e, he, rfl⟩ | ⟨k, hk, rfl⟩ | rfl | ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩)
  · exact ne_of_two_part hm (two_part_ordTrialityD4 he) (h12 e) rfl
  · exact ne_of_two_part hm (two_part_ordTwistedF4 (by omega)) (h12 _) rfl
  · exact ne_of_two_part hm ⟨8775, by decide, ordTits_eq⟩ h11 rfl
  · exact ne_of_two_part hm (two_part_ordTwistedA_three he) (h6 e) rfl
  · exact ne_of_two_part hm (two_part_ordTwistedA_four he) (h10 e) rfl

theorem not_excludedOrder_ordA_two {n : ℕ} (hn : 1 ≤ n) : ¬ ExcludedOrder (ordA 2 (2 ^ n)) := by
  rintro (⟨e, he, h⟩ | ⟨k, hk, h⟩ | h | ⟨e, he, h⟩ | ⟨e, he, h⟩)
  · exact ordA_two_ne_ordTrialityD4 hn he h
  · exact ordA_two_ne_ordTwistedF4 hn (by omega) h
  · exact ne_of_two_part (two_part_ordA_two hn) ⟨8775, by decide, ordTits_eq⟩ (by omega) h
  · exact ordA_ne_ordTwistedA (by norm_num) hn (by norm_num) he h
  · exact ordA_ne_ordTwistedA (by norm_num) hn (by norm_num) he h

theorem not_excludedOrder_ordBC_two {n : ℕ} (hn : 1 ≤ n) : ¬ ExcludedOrder (ordBC 2 (2 ^ n)) := by
  rintro (⟨e, he, h⟩ | ⟨k, hk, h⟩ | h | ⟨e, he, h⟩ | ⟨e, he, h⟩)
  · exact ordTrialityD4_ne_ordBC_two he hn h.symm
  · exact ordTwistedF4_ne_ordBC_two (by omega) hn h.symm
  · exact ordTits_ne_ordBC_two hn h.symm
  · exact CFSG.RankThree.PartOne.S12K.ordTwistedA_ne_ordBC_two (by norm_num) he hn h.symm
  · exact CFSG.RankThree.PartOne.S12K.ordTwistedA_ne_ordBC_two (by norm_num) he hn h.symm

theorem not_excludedOrder_ordG2 {n : ℕ} (hn : 2 ≤ n) : ¬ ExcludedOrder (ordG2 (2 ^ n)) := by
  rintro (⟨e, he, h⟩ | ⟨k, hk, h⟩ | h | ⟨e, he, h⟩ | ⟨e, he, h⟩)
  · exact ordG2_ne_ordTrialityD4 (by omega) he h
  · exact Vol2.Ch11.SecB.ordTwistedF4_ne_ordG2 ⟨k, rfl⟩ (by omega) h.symm
  · exact ne_of_two_part (two_part_ordG2 (by omega)) ⟨8775, by decide, ordTits_eq⟩ (by omega) h
  · exact ordG2_ne_ordTwistedA hn (by norm_num) he h
  · exact ordG2_ne_ordTwistedA hn (by norm_num) he h

theorem not_excludedOrder_360 : ¬ ExcludedOrder 360 :=
  not_excludedOrder_of_two_part (N := 3) ⟨45, by decide, by norm_num⟩ (fun e => by omega)
    (by omega) (fun e => by omega) (fun e => by omega)

theorem not_excludedOrder_6048 : ¬ ExcludedOrder 6048 :=
  not_excludedOrder_of_two_part (N := 5) ⟨189, by decide, by norm_num⟩ (fun e => by omega)
    (by omega) (fun e => by omega) (fun e => by omega)

section Cards


variable {Y : Type} [Group Y]

theorem card_cases_of_isRankTwoLie2Derived (h : IsRankTwoLie2Derived Y) :
    (∃ e, 1 ≤ e ∧ IsPSL 3 2 e Y ∧ Nat.card Y = ordA 2 (2 ^ e)) ∨
    (∃ e, 1 ≤ e ∧ Nat.card Y = ordTwistedA 3 (2 ^ e)) ∨
    (∃ e, 1 ≤ e ∧ Nat.card Y = ordTwistedA 4 (2 ^ e)) ∨
    (∃ e, 2 ≤ e ∧ Nat.card Y = ordBC 2 (2 ^ e)) ∨ Nat.card Y = 360 ∨
    (∃ e, 2 ≤ e ∧ Nat.card Y = ordG2 (2 ^ e)) ∨ Nat.card Y = 6048 ∨
    (∃ e, 1 ≤ e ∧ Nat.card Y = ordTrialityD4 (2 ^ e)) ∨
    (∃ k, 1 ≤ k ∧ Nat.card Y = ordTwistedF4 (2 ^ (2 * k + 1))) ∨ Nat.card Y = ordTits := by
  rcases h with ⟨e, he⟩ | ⟨e, he⟩ | ⟨e, he⟩ | ⟨e, he⟩ | hA | ⟨e, he⟩ | he | ⟨e, he⟩ | ⟨e, he⟩ |
    he
  · exact Or.inl ⟨e, he.1.2.1, he, (card_statedClassicalModel_two he).1 rfl⟩
  · exact Or.inr (Or.inl ⟨e, he.1.2.1, (card_statedClassicalModel_two he).2.1 rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨e, he.1.2.1, (card_statedClassicalModel_two he).2.1 rfl⟩))
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨e, ?_, (card_statedClassicalModel_two he).2.2.1 rfl⟩)))
    obtain ⟨⟨-, he1, -, h22⟩, -⟩ := he
    by_contra hlt
    exact h22 (by rw [show e = 1 by omega]; rfl)
  · obtain ⟨φ⟩ := hA
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
    rw [Nat.card_congr φ.toEquiv, H13.card_alternatingGroup_fin 6 (by norm_num)]
    decide
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨e, ?_, card_chevalleyExceptionalModel_two he⟩)))))
    obtain ⟨⟨-, he1, -, h3⟩, -⟩ := he
    by_contra hc
    rw [show e = 1 by omega] at h3
    norm_num at h3
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (H13.card_of_statedClassicalModel_psu_three_three he)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨e, he.1.2.1, card_chevalleyExceptionalModel_two he⟩)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (H13.card_eq_ordTwistedF4_of_reeTitsModel he)))))))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))))))
    obtain ⟨φ⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv Y 2 1 he
    rw [Nat.card_congr φ.toEquiv, CFSG.Sporadic.Schreier.Tits.card_titsD, ordTits_eq]
    norm_num

theorem excludedOrder_card (h : FFExcludedType Y) : ExcludedOrder (Nat.card Y) := by
  rcases h with ⟨e, he⟩ | ⟨e, he⟩ | he | ⟨e, he⟩ | ⟨e, he⟩
  · exact Or.inl ⟨e, he.1.2.1, card_chevalleyExceptionalModel_two he⟩
  · exact Or.inr (Or.inl (H13.card_eq_ordTwistedF4_of_reeTitsModel he))
  · refine Or.inr (Or.inr (Or.inl ?_))
    obtain ⟨φ⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv Y 2 1 he
    rw [Nat.card_congr φ.toEquiv, CFSG.Sporadic.Schreier.Tits.card_titsD, ordTits_eq]
    norm_num
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨e, he.1.2.1, (card_statedClassicalModel_two he).2.1 rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      ⟨e, he.1.2.1, (card_statedClassicalModel_two he).2.1 rfl⟩)))

theorem card_eq_168_or_rankTwoOrder (h : IsRankTwoLie2Derived Y) :
    Nat.card Y = 168 ∨ RankTwoOrder (Nat.card Y) := by
  rcases card_cases_of_isRankTwoLie2Derived h with ⟨e, he, -, hc⟩ | ⟨e, he, hc⟩ | ⟨e, he, hc⟩ |
    ⟨e, he, hc⟩ | hc | ⟨e, he, hc⟩ | hc | ⟨e, he, hc⟩ | ⟨k, hk, hc⟩ | hc
  · rcases Nat.lt_or_ge e 2 with h1 | h2
    · rw [show e = 1 by omega] at hc
      exact Or.inl (by rw [hc]; decide)
    · exact Or.inr (Or.inl ⟨e, h2, hc⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨e, he, hc⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e, he, hc⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, by omega, hc⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hc)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, he, hc⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hc)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨e, he, hc⟩))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨k, hk, hc⟩)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      hc)))))))))

theorem card_ne_ordA_one (h : IsRankTwoLie2Derived Y) {n : ℕ} (hn : 2 ≤ n) :
    Nat.card Y ≠ ordA 1 (2 ^ n) := by
  intro hc
  rcases card_eq_168_or_rankTwoOrder h with h168 | hR
  · rw [h168] at hc
    by_cases h3 : n = 3
    · subst h3
      revert hc
      decide
    · exact ne_of_two_part (two_part_ordA_one (by omega)) ⟨21, by decide, by norm_num⟩ h3 hc.symm
  · rw [hc] at hR
    exact ordA_one_two_pow_not_rankTwoOrder hn hR

theorem card_ne_2520 (h : IsRankTwoLie2Derived Y) : Nat.card Y ≠ 2520 := by
  have hm : ∃ r, Odd r ∧ (2520 : ℕ) = 2 ^ 3 * r := ⟨315, by decide, by norm_num⟩
  intro hc
  rcases card_cases_of_isRankTwoLie2Derived h with ⟨e, he, -, h1⟩ | ⟨e, he, h1⟩ | ⟨e, he, h1⟩ |
    ⟨e, he, h1⟩ | h1 | ⟨e, he, h1⟩ | h1 | ⟨e, he, h1⟩ | ⟨k, hk, h1⟩ | h1 <;> rw [hc] at h1
  · rcases Nat.lt_or_ge e 2 with h2 | h2
    · rw [show e = 1 by omega] at h1
      revert h1
      decide
    · exact ne_of_two_part hm (two_part_ordA_two he) (by omega) h1
  · exact ne_of_two_part hm (two_part_ordTwistedA_three he) (by omega) h1
  · exact ne_of_two_part hm (two_part_ordTwistedA_four he) (by omega) h1
  · exact ne_of_two_part hm (two_part_ordBC_two (by omega)) (by omega) h1
  · norm_num at h1
  · exact ne_of_two_part hm (two_part_ordG2 (by omega)) (by omega) h1
  · norm_num at h1
  · exact ne_of_two_part hm (two_part_ordTrialityD4 he) (by omega) h1
  · exact ne_of_two_part hm (two_part_ordTwistedF4 (by omega)) (by omega) h1
  · rw [ordTits_eq] at h1
    norm_num at h1

theorem card_ne_9999360 (h : IsRankTwoLie2Derived Y) : Nat.card Y ≠ 9999360 := by
  have hm : ∃ r, Odd r ∧ (9999360 : ℕ) = 2 ^ 10 * r := ⟨9765, by decide, by norm_num⟩
  intro hc
  rcases card_cases_of_isRankTwoLie2Derived h with ⟨e, he, -, h1⟩ | ⟨e, he, h1⟩ | ⟨e, he, h1⟩ |
    ⟨e, he, h1⟩ | h1 | ⟨e, he, h1⟩ | h1 | ⟨e, he, h1⟩ | ⟨k, hk, h1⟩ | h1 <;> rw [hc] at h1
  · exact ne_of_two_part hm (two_part_ordA_two he) (by omega) h1
  · exact ne_of_two_part hm (two_part_ordTwistedA_three he) (by omega) h1
  · rcases Nat.lt_or_ge e 2 with h2 | h2
    · rw [show e = 1 by omega] at h1
      revert h1
      decide
    · exact ne_of_two_part hm (two_part_ordTwistedA_four he) (by omega) h1
  · exact ne_of_two_part hm (two_part_ordBC_two (by omega)) (by omega) h1
  · norm_num at h1
  · exact ne_of_two_part hm (two_part_ordG2 (by omega)) (by omega) h1
  · norm_num at h1
  · exact ne_of_two_part hm (two_part_ordTrialityD4 he) (by omega) h1
  · exact ne_of_two_part hm (two_part_ordTwistedF4 (by omega)) (by omega) h1
  · rw [ordTits_eq] at h1
    norm_num at h1

theorem isPSL_three_two_two_of_card (h : IsRankTwoLie2Derived Y) (hc : Nat.card Y = 20160) :
    IsPSL 3 2 2 Y := by
  have hm : ∃ r, Odd r ∧ (20160 : ℕ) = 2 ^ 6 * r := ⟨315, by decide, by norm_num⟩
  rcases card_cases_of_isRankTwoLie2Derived h with ⟨e, he, hP, h1⟩ | ⟨e, he, h1⟩ | ⟨e, he, h1⟩ |
    ⟨e, he, h1⟩ | h1 | ⟨e, he, h1⟩ | h1 | ⟨e, he, h1⟩ | ⟨k, hk, h1⟩ | h1 <;> rw [hc] at h1
  · by_cases he2 : e = 2
    · exact he2 ▸ hP
    · exact (ne_of_two_part hm (two_part_ordA_two he) (by omega) h1).elim
  · rcases Nat.lt_or_ge e 2 with h2 | h2
    · rw [show e = 1 by omega] at h1
      exact absurd h1 (by decide)
    · exact (ne_of_two_part hm (two_part_ordTwistedA_three he) (by omega) h1).elim
  · exact (ne_of_two_part hm (two_part_ordTwistedA_four he) (by omega) h1).elim
  · exact (ne_of_two_part hm (two_part_ordBC_two (by omega)) (by omega) h1).elim
  · norm_num at h1
  · exact (ne_of_two_part hm (two_part_ordG2 (by omega)) (by omega) h1).elim
  · norm_num at h1
  · exact (ne_of_two_part hm (two_part_ordTrialityD4 he) (by omega) h1).elim
  · exact (ne_of_two_part hm (two_part_ordTwistedF4 (by omega)) (by omega) h1).elim
  · rw [ordTits_eq] at h1
    norm_num at h1

end Cards

end CFSG.Quasithin.MS93
