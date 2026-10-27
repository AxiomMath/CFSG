module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
public import CFSG.Adapters.LieModelSimple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s13_Facts13_two_pow_sub_one_mod_three {s : ℕ} (hs : Odd s) :
    (2 ^ s - 1) % 3 = 1 := by
  obtain ⟨k, rfl⟩ := hs
  have h : 2 ^ (2 * k + 1) = 4 ^ k * 2 := by rw [pow_succ, pow_mul]; norm_num
  have hp : 4 ^ k * 2 ≡ 2 [MOD 3] := by
    have h1 : 4 ^ k * 2 ≡ 1 ^ k * 2 [MOD 3] :=
      ((show (4 : ℕ) ≡ 1 [MOD 3] by decide).pow k).mul rfl
    rwa [one_pow, one_mul] at h1
  have hle : 1 ≤ 4 ^ k * 2 := by
    simpa using Nat.mul_le_mul (Nat.one_le_pow k 4 (by norm_num))
      (show (1 : ℕ) ≤ 2 by norm_num)
  have h1 : 4 ^ k * 2 - 1 ≡ 1 [MOD 3] := Nat.ModEq.sub hle (by norm_num) hp rfl
  rw [h]
  exact h1

theorem s13_Facts13_four_pow_modeq_five (k : ℕ) : 4 ^ k ≡ 1 [MOD 5] ∨ 4 ^ k ≡ 4 [MOD 5] := by
  induction k with
  | zero => left; decide
  | succ n ih =>
    rw [pow_succ]
    rcases ih with h | h
    · right
      have h1 : 4 ^ n * 4 ≡ 1 * 4 [MOD 5] := h.mul rfl
      rwa [one_mul] at h1
    · left
      have h1 : 4 ^ n * 4 ≡ 4 * 4 [MOD 5] := h.mul rfl
      exact h1.trans (by decide : (4 * 4 : ℕ) ≡ 1 [MOD 5])

theorem s13_Facts13_two_pow_mod_five_ne {s : ℕ} (hs : Odd s) : (2 ^ s - 1) % 5 ≠ 0 := by
  obtain ⟨k, rfl⟩ := hs
  have h : 2 ^ (2 * k + 1) = 4 ^ k * 2 := by rw [pow_succ, pow_mul]; norm_num
  have hle : 1 ≤ 4 ^ k * 2 := by
    simpa using Nat.mul_le_mul (Nat.one_le_pow k 4 (by norm_num))
      (show (1 : ℕ) ≤ 2 by norm_num)
  rw [h]
  rcases s13_Facts13_four_pow_modeq_five k with hk | hk
  · have hp : 4 ^ k * 2 ≡ 2 [MOD 5] := by
      have h1 : 4 ^ k * 2 ≡ 1 * 2 [MOD 5] := hk.mul rfl
      rwa [one_mul] at h1
    have h1 : 4 ^ k * 2 - 1 ≡ 1 [MOD 5] := Nat.ModEq.sub hle (by norm_num) hp rfl
    rw [show (4 ^ k * 2 - 1) % 5 = 1 from h1]
    norm_num
  · have hp : 4 ^ k * 2 ≡ 3 [MOD 5] := by
      have h1 : 4 ^ k * 2 ≡ 4 * 2 [MOD 5] := hk.mul rfl
      exact h1.trans (by decide : (4 * 2 : ℕ) ≡ 3 [MOD 5])
    have h1 : 4 ^ k * 2 - 1 ≡ 2 [MOD 5] :=
      Nat.ModEq.sub hle (by norm_num : (1 : ℕ) ≤ 3) hp rfl
    rw [show (4 ^ k * 2 - 1) % 5 = 2 from h1]
    norm_num

theorem s13_seven_le_of_dvd {s r : ℕ} (hs : Odd s) (hr : r.Prime) (hrd : r ∣ 2 ^ s - 1) :
    7 ≤ r := by
  have hs0 : s ≠ 0 := by obtain ⟨k, hk⟩ := hs; omega
  have h2 : r ≠ 2 := by
    rintro rfl
    have heven : Even (2 ^ s) := (Nat.even_pow' hs0).2 even_two
    have hodd : Odd (2 ^ s - 1) :=
      Nat.Even.sub_odd (Nat.one_le_pow s 2 (by norm_num)) heven odd_one
    have h1 : (2 ^ s - 1) % 2 = 1 := Nat.odd_iff.mp hodd
    have h0 : (2 ^ s - 1) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hrd
    omega
  have h3 : r ≠ 3 := by
    rintro rfl
    have h1 : (2 ^ s - 1) % 3 = 1 := s13_Facts13_two_pow_sub_one_mod_three hs
    have h0 : (2 ^ s - 1) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp hrd
    omega
  have h5 : r ≠ 5 := by
    rintro rfl
    exact s13_Facts13_two_pow_mod_five_ne hs (Nat.dvd_iff_mod_eq_zero.mp hrd)
  have h5le : 5 ≤ r := hr.five_le_of_ne_two_of_ne_three h2 h3
  by_contra h
  rw [not_le] at h
  interval_cases r
  · exact h5 rfl
  · norm_num at hr

theorem s13_exists_odd_divisor {n : ℕ} (hn : ¬ IsPowTwo n) :
    ∃ s : ℕ, Odd s ∧ 1 < s ∧ s ∣ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · exact ⟨3, ⟨1, by norm_num⟩, by norm_num, dvd_zero 3⟩
  · obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn0.ne'
    have hm1 : m ≠ 1 := by
      intro h1
      exact hn ⟨k, by rw [h1, mul_one]⟩
    have hm0 : m ≠ 0 := by
      obtain ⟨j, hj⟩ := hm
      omega
    refine ⟨m, hm, ?_, dvd_mul_left m (2 ^ k)⟩
    omega

theorem s13_exists_prime_dvd {s : ℕ} (hs : 1 < s) : ∃ r : ℕ, r.Prime ∧ r ∣ 2 ^ s - 1 := by
  have h2 : 4 ≤ 2 ^ s := by
    have h := Nat.pow_le_pow_right (show (1 : ℕ) ≤ 2 by norm_num) hs
    norm_num at h
    exact h
  exact Nat.exists_prime_and_dvd (by omega : 2 ^ s - 1 ≠ 1)

theorem s13_not_isPowTwo_of_prime {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) : ¬ IsPowTwo r := by
  rintro ⟨k, hk⟩
  exact hr2 (hr.pow_eq_iff.1 hk.symm).1.symm

theorem s13_odd_divisor_self {n : ℕ} (hn : Odd n) (hpow : ¬ IsPowTwo n) :
    Odd n ∧ 1 < n ∧ n ∣ n := by
  refine ⟨hn, ?_, dvd_refl n⟩
  have hn0 : n ≠ 0 := by
    obtain ⟨j, hj⟩ := hn
    omega
  have hn1 : n ≠ 1 := by
    intro h1
    exact hpow ⟨0, by rw [h1]; norm_num⟩
  omega

theorem s13_two_le_of_isL2 {X : Type} [Group X] {f : ℕ} (h : IsL2 X f) : 2 ≤ f := by
  have hadm := h.admissible
  simp only [CFSG.Open.StatedLieAdmissible] at hadm
  obtain ⟨-, hf, -, hne, -⟩ := hadm
  have hne' : 2 ^ f ≠ 2 := fun hc => hne (by rw [hc])
  have hf1 : f ≠ 1 := by
    intro h1
    exact hne' (by rw [h1]; norm_num)
  omega

theorem s13_two_le_of_isU3 {X : Type} [Group X] {f : ℕ} (h : IsU3 X f) : 2 ≤ f := by
  have hadm := h.admissible
  simp only [CFSG.Open.StatedLieAdmissible] at hadm
  obtain ⟨-, hf, -, hne⟩ := hadm
  have hne' : 2 ^ f ≠ 2 := fun hc => hne (by rw [hc])
  have hf1 : f ≠ 1 := by
    intro h1
    exact hne' (by rw [h1]; norm_num)
  omega

theorem s13_odd_three_le_of_isSz {X : Type} [Group X] {f : ℕ} (h : IsSz X f) :
    Odd f ∧ 3 ≤ f := by
  have hadm := h.admissible
  simp only [CFSG.Open.StatedLieAdmissible] at hadm
  tauto

theorem s13_not_isSz_of_isPowTwo {X : Type} [Group X] {f : ℕ} (h : IsSz X f)
    (hf : IsPowTwo f) : False := by
  obtain ⟨hodd, h3⟩ := s13_odd_three_le_of_isSz h
  obtain ⟨k, rfl⟩ := hf
  cases k with
  | zero => norm_num at h3
  | succ j =>
    have heven : Even (2 ^ (j + 1)) := (Nat.even_pow' (by omega : j + 1 ≠ 0)).2 even_two
    exact (Nat.not_even_iff_odd.mpr hodd) heven

theorem s13_five_le_of_isL2Odd {X : Type} [Group X] {p : ℕ} (h : IsL2Odd X p) :
    p.Prime ∧ p ≠ 2 ∧ 5 ≤ p := by
  have hadm := h.admissible
  simp only [CFSG.Open.StatedLieAdmissible] at hadm
  obtain ⟨hp, -, -, hne2, hne3⟩ := hadm
  have hp2 : p ≠ 2 := fun hc => hne2 (by rw [hc]; norm_num)
  have hp3 : p ≠ 3 := fun hc => hne3 (by rw [hc]; norm_num)
  exact ⟨hp, hp2, hp.five_le_of_ne_two_of_ne_three hp2 hp3⟩

theorem s13_isSimple_of_isU3 {X : Type} [Group X] {f : ℕ} (h : IsU3 X f) : IsSimpleGroup X :=
  CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h

theorem s13_exists_subgroup_of_dvd_card_bar {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {r : ℕ} (hr : r.Prime) (hrd : r ∣ Nat.card (Bar2 L)) :
    ∃ X : Subgroup G, X ≤ L ∧ Nat.card X = r := by
  have hdvd : r ∣ Nat.card ↥L :=
    hrd.trans (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥L))
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' r hdvd
  refine ⟨Subgroup.zpowers (x : G), Subgroup.zpowers_le.2 x.2, ?_⟩
  rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx]

theorem s13_exists_element_of_dvd {Q : Type} [Group Q] [Finite Q] (J : Subgroup Q) {p : ℕ}
    (hp : p.Prime) (hd : p ∣ Nat.card J) : ∃ s ∈ J, orderOf s = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hd
  exact ⟨x, x.2, by rwa [Subgroup.orderOf_coe]⟩

theorem s13_one_le_pRank_of_dvd {Q : Type} [Group Q] [Finite Q] (J : Subgroup Q) {r : ℕ}
    (hr : r.Prime) (hd : r ∣ Nat.card J) : 1 ≤ CFSG.Open.pRank r J := by
  obtain ⟨s, hsJ, hs⟩ := s13_exists_element_of_dvd J hr hd
  refine CFSG.SectionRank.le_pRank (p := r) (H := J) (E := Subgroup.zpowers s) (k := 1)
    hr.one_lt (Subgroup.zpowers_le.2 hsJ) ?_ ?_
  · exact CFSG.Open.isElemAbelian_zpowers (by rw [← hs]; exact pow_orderOf_eq_one s)
  · rw [Nat.card_zpowers, hs, pow_one]

theorem s13_pRank_of_card_prime {Q : Type} [Group Q] [Finite Q] (J : Subgroup Q) {r : ℕ}
    (hr : r.Prime) (hJ : Nat.card J = r) : CFSG.Open.pRank r J = 1 := by
  apply le_antisymm
  · refine CFSG.SectionRank.pRank_le hr.one_lt ?_
    intro E hEJ _
    have hcard : Nat.card E ≤ r := (Subgroup.card_le_of_le hEJ).trans_eq hJ
    calc Nat.card E ≤ r := hcard
      _ = r ^ 1 := (pow_one r).symm
  · exact s13_one_le_pRank_of_dvd J hr (by rw [hJ])

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
