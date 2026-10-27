module

public import CFSG.Quasithin.Vol2.Ch10SecQ1G2Two
public import CFSG.Quasithin.EmptyFaithful.T1515dB
public import CFSG.Timmesfeld.Orders.Distinct
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

@[expose] def B56Card (N : ℕ) : Prop :=
  (∃ n, 1 ≤ n ∧ N = 2 ^ n * ((2 ^ n) ^ 2 - 1)) ∨
    (∃ n, 1 ≤ n ∧ N = (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1))) ∨
    (∃ n, 1 ≤ n ∧ N = (2 ^ n) ^ 4 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1))) ∨
    (∃ n, 1 ≤ n ∧ N = (2 ^ n) ^ 6 * (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1))) ∨
    N = 360 ∨ N = 2520 ∨ N = 1080 ∨ N = 6048 ∨ N = 20160 ∨ N = 9999360

theorem one_le_of_card_field {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    1 ≤ n := by
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  rw [hK] at h1
  rcases n with _ | n
  · simp at h1
  · omega

theorem b56Card_of_list {X : Type} [Group X] [Finite X] (h : B56QuasisimpleList X) :
    B56Card (Nat.card X) := by
  rcases h with ⟨n, K, _, _, hK, ⟨e⟩⟩ | ⟨n, K, _, _, hK, ⟨e⟩⟩ | ⟨n, K, _, _, hK, ⟨e⟩⟩ |
      ⟨n, K, _, _, hK, ⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | h6 | ⟨K, _, _, hK, ⟨e⟩⟩ | h4 | h5
  · refine Or.inl ⟨n, one_le_of_card_field hK, ?_⟩
    rw [Nat.card_congr e.toEquiv, card_statedSL_two1527d, hK]
  · refine Or.inr (Or.inl ⟨n, one_le_of_card_field hK, ?_⟩)
    rw [Nat.card_congr e.toEquiv, card_statedSL_three1527d, hK]
  · refine Or.inr (Or.inr (Or.inl ⟨n, one_le_of_card_field hK, ?_⟩))
    rw [Nat.card_congr e.toEquiv, CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp,
      hK]
    have hI : Finset.Icc 1 2 = {1, 2} := by decide
    rw [hI, Finset.prod_pair (by norm_num), show (2 : ℕ) ^ 2 = 4 by norm_num,
      show 2 * 1 = 2 by norm_num, show 2 * 2 = 4 by norm_num]
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨n, one_le_of_card_field hK, ?_⟩)))
    rw [Nat.card_congr e.toEquiv, card_quasithinG2_1527d hK, hK]
  · iterate 4 right
    left
    rw [Nat.card_congr e.toEquiv, card_alternatingGroup1527d 6 (by norm_num)]
    decide
  · iterate 5 right
    left
    rw [Nat.card_congr e.toEquiv, card_alternatingGroup1527d 7 (by norm_num)]
    decide
  · iterate 6 right
    left
    exact card_of_isHat1527d h6 (by rw [card_alternatingGroup1527d 6 (by norm_num)]; decide)
  · iterate 7 right
    left
    rw [Nat.card_congr e.toEquiv, SecA.C10P01.card_g2Two_commutator hK]
  · iterate 8 right
    left
    obtain ⟨e⟩ := h4
    rw [Nat.card_congr e.toEquiv, card_statedSL_four_zmod1527d]
  · iterate 9 right
    obtain ⟨e⟩ := h5
    rw [Nat.card_congr e.toEquiv, card_statedSL_five_zmod1527d]

theorem eq_and_eq_of_two_pow_mul {a b r s : ℕ} (hr : Odd r) (hs : Odd s)
    (h : 2 ^ a * r = 2 ^ b * s) : a = b ∧ r = s := by
  have hab := CFSG.Timmesfeld.Orders.eq_of_two_pow_mul_odd hr hs h
  subst hab
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (by positivity) h⟩

theorem odd_two_pow_pow_sub_one {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) : Odd ((2 ^ n) ^ k - 1) :=
  CFSG.Timmesfeld.Orders.odd_pow_sub_one (by omega) (by omega)

theorem B56Card.cases {N v u : ℕ} (h : B56Card N) (hN : N = 2 ^ v * u) (hu : Odd u) :
    (1 ≤ v ∧ u = (2 ^ v) ^ 2 - 1) ∨
      (∃ n, 1 ≤ n ∧ v = 3 * n ∧ u = ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) ∨
      (∃ n, 1 ≤ n ∧ v = 4 * n ∧ u = ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1)) ∨
      (∃ n, 1 ≤ n ∧ v = 6 * n ∧ u = ((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1)) ∨
      N = 360 ∨ N = 2520 ∨ N = 1080 ∨ N = 6048 ∨ N = 20160 ∨ N = 9999360 := by
  rcases h with ⟨n, hn, h⟩ | ⟨n, hn, h⟩ | ⟨n, hn, h⟩ | ⟨n, hn, h⟩ | h
  · obtain ⟨rfl, rfl⟩ := eq_and_eq_of_two_pow_mul (odd_two_pow_pow_sub_one hn (by norm_num))
      hu (h.symm.trans hN)
    exact Or.inl ⟨hn, rfl⟩
  · have e : (2 : ℕ) ^ (3 * n) = (2 ^ n) ^ 3 := by rw [mul_comm, pow_mul]
    have h' : 2 ^ (3 * n) * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) = 2 ^ v * u := by
      rw [e, ← h]
      exact hN
    obtain ⟨rfl, rfl⟩ := eq_and_eq_of_two_pow_mul ((odd_two_pow_pow_sub_one hn (by norm_num)).mul
      (odd_two_pow_pow_sub_one hn (by norm_num))) hu h'
    exact Or.inr (Or.inl ⟨n, hn, rfl, rfl⟩)
  · have e : (2 : ℕ) ^ (4 * n) = (2 ^ n) ^ 4 := by rw [mul_comm, pow_mul]
    have h' : 2 ^ (4 * n) * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1)) = 2 ^ v * u := by
      rw [e, ← h]
      exact hN
    obtain ⟨rfl, rfl⟩ := eq_and_eq_of_two_pow_mul ((odd_two_pow_pow_sub_one hn (by norm_num)).mul
      (odd_two_pow_pow_sub_one hn (by norm_num))) hu h'
    exact Or.inr (Or.inr (Or.inl ⟨n, hn, rfl, rfl⟩))
  · have e : (2 : ℕ) ^ (6 * n) = (2 ^ n) ^ 6 := by rw [mul_comm, pow_mul]
    have h' : 2 ^ (6 * n) * (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1)) = 2 ^ v * u := by
      rw [e, ← h]
      exact hN
    obtain ⟨rfl, rfl⟩ := eq_and_eq_of_two_pow_mul ((odd_two_pow_pow_sub_one hn (by norm_num)).mul
      (odd_two_pow_pow_sub_one hn (by norm_num))) hu h'
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, rfl, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
