module

import CFSG.RankThree.PartTwo.Sec19.Step1911Proof
import CFSG.RankThree.PartOne.S12K.Rigidity
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
public import CFSG.RankThree.PartTwo.Sec4.Item419Res2ProofTools
public import CFSG.RankThree.PartTwo.Sec4.Item4Res3Proof419

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item419Res3

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.Blueprint
open CFSG.Assembly.RankThreeEven (projSU projSp)

theorem isType419_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsType419 Y) : IsType419 X := by
  rcases h with ⟨n, hG2⟩ | hU | ⟨n, hF4⟩ | hT | ⟨n, hn, ⟨e'⟩⟩ | hA
  · exact Or.inl ⟨n, CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv e hG2⟩
  · obtain ⟨e'⟩ := hU
    exact Or.inr (Or.inl ⟨e.trans e'⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨n, CFSG.SectionRank.reeTitsModel_of_mulEquiv e hF4⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (CFSG.SectionRank.reeTitsModel_of_mulEquiv e hT))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, ⟨e.trans e'⟩⟩))))
  · obtain ⟨e'⟩ := hA
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e.trans e'⟩))))

theorem padicValNat_two_pow_mul_odd {a u : ℕ} (hu : Odd u) : padicValNat 2 (2 ^ a * u) = a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu2 : ¬ 2 ∣ u := by
    obtain ⟨k, rfl⟩ := hu
    omega
  rw [padicValNat.mul (by positivity) hu.pos.ne', padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hu2, add_zero]

theorem eq_of_two_pow_mul_odd {a b u v : ℕ} (hu : Odd u) (hv : Odd v)
    (h : 2 ^ a * u = 2 ^ b * v) : a = b ∧ u = v := by
  have hab : a = b := by
    have h1 := congrArg (padicValNat 2) h
    rwa [padicValNat_two_pow_mul_odd hu, padicValNat_two_pow_mul_odd hv] at h1
  subst hab
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (by positivity) h⟩

theorem odd_two_pow_pow_sub_one {n j : ℕ} (hn : 1 ≤ n) (hj : 1 ≤ j) : Odd ((2 ^ n) ^ j - 1) := by
  have he : Even ((2 ^ n) ^ j) := by
    rw [← pow_mul]
    exact (Nat.even_pow.mpr ⟨even_two, by positivity⟩)
  have h1 : 1 ≤ (2 ^ n) ^ j := Nat.one_le_pow _ _ (by positivity)
  exact Nat.Even.sub_odd h1 he odd_one

theorem odd_two_pow_pow_add_one {n j : ℕ} (hn : 1 ≤ n) (hj : 1 ≤ j) : Odd ((2 ^ n) ^ j + 1) := by
  have he : Even ((2 ^ n) ^ j) := by
    rw [← pow_mul]
    exact (Nat.even_pow.mpr ⟨even_two, by positivity⟩)
  exact he.add_one

theorem card_two_part_of_isType419
    {K : Type} [Group K]
    (h : IsType419 K) :
    (∃ n : ℕ, 2 ≤ n ∧ Nat.card K = 2 ^ (6 * n) * (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1))) ∨
    (∃ n : ℕ, 1 ≤ n ∧ ∃ u : ℕ, Odd u ∧ Nat.card K = 2 ^ (12 * n) * u) ∨
    Nat.card K = 2 ^ 11 * 8775 ∨
    (∃ n : ℕ, 2 ≤ n ∧ ∃ u : ℕ, Odd u ∧ Nat.card K = 2 ^ (4 * n) * u) ∨
    Nat.card K = 2 ^ 5 * 189 ∨ Nat.card K = 2 ^ 3 * 45 := by
  rcases h with ⟨n, hG2⟩ | hU | ⟨n, hF4⟩ | hT | ⟨n, hn, ⟨e⟩⟩ | hA
  · left
    have hn : 2 ≤ n := by
      obtain ⟨⟨-, -, -, h3⟩, -⟩ := hG2
      by_contra hlt
      interval_cases n <;> simp at h3
    refine ⟨n, hn, ?_⟩
    rw [(CFSG.Timmesfeld.card_chevalleyExceptionalModel_untwisted hG2).1 rfl, CFSG.Open.ordG2,
      mul_assoc, ← pow_mul, mul_comm n 6]
  · right; right; right; right; left
    obtain ⟨e⟩ := hU
    rw [Nat.card_congr e.toEquiv,
      CFSG.RankThree.PartTwo.Sec19.Step1911Proof.card_projSU_three_three]
    norm_num
  · right; left
    have hn : 1 ≤ n := hF4.1.2.1
    refine ⟨n, hn, ((2 ^ n) ^ 6 + 1) * ((2 ^ n) ^ 4 - 1) * ((2 ^ n) ^ 3 + 1) * (2 ^ n - 1),
      ?_, ?_⟩
    · have h1 : Odd (2 ^ n - 1) := by
        simpa using odd_two_pow_pow_sub_one (j := 1) hn le_rfl
      exact (((odd_two_pow_pow_add_one hn (by norm_num)).mul
        (odd_two_pow_pow_sub_one hn (by norm_num))).mul
          (odd_two_pow_pow_add_one hn (by norm_num))).mul h1
    · rw [CFSG.RankThree.PartOne.S12K.card_of_reeTitsModel_twistedF4 hF4, CFSG.Open.ordTwistedF4,
        mul_comm 12 n, pow_mul]
      ring
  · right; right; left
    rw [CFSG.RankThree.PartOne.S12K.card_of_reeTitsModel_Tits hT, CFSG.Open.ordTits]
    norm_num
  · right; right; right; left
    refine ⟨n, hn, ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1),
      (odd_two_pow_pow_sub_one (by omega) (by norm_num)).mul
        (odd_two_pow_pow_sub_one (by omega) (by norm_num)), ?_⟩
    rw [Nat.card_congr e.toEquiv,
      CFSG.RankThree.PartTwo.Sec19.Step1911Proof.card_projSp_two (by omega), mul_comm 4 n]
  · right; right; right; right; right
    obtain ⟨e⟩ := hA
    rw [Nat.card_congr e.toEquiv, Res4Three419.card_alternatingGroup_six]
    norm_num

theorem card_ne_sl2_of_isType419
    {K : Type} [Group K]
    (h : IsType419 K) {m : ℕ} (hm : Odd m) : Nat.card K ≠ 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
  intro hK
  have hm1 : 1 ≤ m := hm.pos
  have hodd : Odd ((2 ^ m) ^ 2 - 1) := odd_two_pow_pow_sub_one hm1 (by norm_num)
  rcases card_two_part_of_isType419 h with ⟨n, hn, hc⟩ | ⟨n, hn, u, hu, hc⟩ | hc |
      ⟨n, hn, u, hu, hc⟩ | hc | hc
  · have hu : Odd (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1)) :=
      (odd_two_pow_pow_sub_one (by omega) (by norm_num)).mul
        (odd_two_pow_pow_sub_one (by omega) (by norm_num))
    have := (eq_of_two_pow_mul_odd hu hodd (hc.symm.trans hK)).1
    obtain ⟨j, hj⟩ := hm
    omega
  · have := (eq_of_two_pow_mul_odd hu hodd (hc.symm.trans hK)).1
    obtain ⟨j, hj⟩ := hm
    omega
  · have h2 := eq_of_two_pow_mul_odd (by decide) hodd (hc.symm.trans hK)
    obtain ⟨rfl, h3⟩ := h2
    norm_num at h3
  · have := (eq_of_two_pow_mul_odd hu hodd (hc.symm.trans hK)).1
    obtain ⟨j, hj⟩ := hm
    omega
  · have h2 := eq_of_two_pow_mul_odd (by decide) hodd (hc.symm.trans hK)
    obtain ⟨rfl, h3⟩ := h2
    norm_num at h3
  · have h2 := eq_of_two_pow_mul_odd (by decide) hodd (hc.symm.trans hK)
    obtain ⟨rfl, h3⟩ := h2
    norm_num at h3

theorem sq_six_sub_one_ne {q : ℕ} (hq : 2 ≤ q) : q ^ 6 - 1 ≠ (q ^ 3 + 1) * (q ^ 4 - 1) := by
  intro h
  have h1 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ (by omega)
  zify [h1, h2] at h
  have h3 : ((q : ℤ) ^ 3 + 1) * ((q : ℤ) ^ 3 * ((q : ℤ) - 1)) = 0 := by linear_combination -h
  have hq' : (2 : ℤ) ≤ q := by exact_mod_cast hq
  have h4 : ((q : ℤ) ^ 3 + 1) * ((q : ℤ) ^ 3 * ((q : ℤ) - 1)) > 0 :=
    mul_pos (by positivity) (mul_pos (by positivity) (by linarith))
  linarith

theorem card_ne_u4_of_isType419
    {K : Type} [Group K]
    (h : IsType419 K) {k : ℕ} (hk : Odd k) :
    Nat.card K ≠ (2 ^ k) ^ 6 * (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 3 + 1) * ((2 ^ k) ^ 4 - 1)) := by
  intro hK
  have hk1 : 1 ≤ k := hk.pos
  have hodd : Odd (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 3 + 1) * ((2 ^ k) ^ 4 - 1)) :=
    ((odd_two_pow_pow_sub_one hk1 (by norm_num)).mul
      (odd_two_pow_pow_add_one hk1 (by norm_num))).mul (odd_two_pow_pow_sub_one hk1 (by norm_num))
  rw [← pow_mul] at hK
  rcases card_two_part_of_isType419 h with ⟨n, hn, hc⟩ | ⟨n, hn, u, hu, hc⟩ | hc |
      ⟨n, hn, u, hu, hc⟩ | hc | hc
  · have hu : Odd (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1)) :=
      (odd_two_pow_pow_sub_one (by omega) (by norm_num)).mul
        (odd_two_pow_pow_sub_one (by omega) (by norm_num))
    obtain ⟨h1, h2⟩ := eq_of_two_pow_mul_odd hu hodd (hc.symm.trans hK)
    have hnk : n = k := by omega
    subst hnk
    have hq : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpos : 0 < (2 ^ n) ^ 2 - 1 := by
      have : 4 ≤ (2 ^ n) ^ 2 := by nlinarith
      omega
    have h3 : ((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1) =
        ((2 ^ n) ^ 3 + 1) * ((2 ^ n) ^ 4 - 1) * ((2 ^ n) ^ 2 - 1) := by
      rw [h2]; ring
    exact sq_six_sub_one_ne hq (Nat.eq_of_mul_eq_mul_right hpos h3)
  · have := (eq_of_two_pow_mul_odd hu hodd (hc.symm.trans hK)).1
    obtain ⟨j, hj⟩ := hk
    omega
  · have := (eq_of_two_pow_mul_odd (by decide) hodd (hc.symm.trans hK)).1
    omega
  · have := (eq_of_two_pow_mul_odd hu hodd (hc.symm.trans hK)).1
    obtain ⟨j, hj⟩ := hk
    omega
  · have := (eq_of_two_pow_mul_odd (by decide) hodd (hc.symm.trans hK)).1
    omega
  · have := (eq_of_two_pow_mul_odd (by decide) hodd (hc.symm.trans hK)).1
    omega

end CFSG.RankThree.PartTwo.Sec4.Item419Res3
