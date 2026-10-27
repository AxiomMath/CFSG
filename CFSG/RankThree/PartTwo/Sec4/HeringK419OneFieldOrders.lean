module

public import CFSG.RankThree.PartTwo.Sec4.Item419Res3ProofOrders
import CFSG.RankThree.PartTwo.Sec19.Step1911Proof
import CFSG.RankThree.PartOne.S12K.Rigidity

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item419Res3

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.Blueprint
open CFSG.Assembly.RankThreeEven (projSU projSp)

section Types


theorem card_isType419_explicit {K : Type} [Group K] (h : IsType419 K) :
    (∃ n : ℕ, 2 ≤ n ∧
      Nat.card K = (2 ^ n) ^ 6 * (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1))) ∨
    (∃ n : ℕ, 1 ≤ n ∧ Nat.card K = (2 ^ n) ^ 12 *
      (((2 ^ n) ^ 6 + 1) * ((2 ^ n) ^ 4 - 1) * ((2 ^ n) ^ 3 + 1) * (2 ^ n - 1))) ∨
    Nat.card K = 2 ^ 11 * 8775 ∨
    (∃ n : ℕ, 2 ≤ n ∧ Nat.card K = (2 ^ n) ^ 4 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1))) ∨
    Nat.card K = 2 ^ 5 * 189 ∨ Nat.card K = 2 ^ 3 * 45 := by
  rcases h with ⟨n, hG2⟩ | hU | ⟨n, hF4⟩ | hT | ⟨n, hn, ⟨e⟩⟩ | hA
  · left
    have hn : 2 ≤ n := by
      obtain ⟨⟨-, -, -, h3⟩, -⟩ := hG2
      by_contra hlt
      interval_cases n <;> simp at h3
    refine ⟨n, hn, ?_⟩
    rw [(CFSG.Timmesfeld.card_chevalleyExceptionalModel_untwisted hG2).1 rfl, CFSG.Open.ordG2]
    ring
  · right; right; right; right; left
    obtain ⟨e⟩ := hU
    rw [Nat.card_congr e.toEquiv,
      CFSG.RankThree.PartTwo.Sec19.Step1911Proof.card_projSU_three_three]
    norm_num
  · right; left
    have hn : 1 ≤ n := hF4.1.2.1
    refine ⟨n, hn, ?_⟩
    rw [CFSG.RankThree.PartOne.S12K.card_of_reeTitsModel_twistedF4 hF4, CFSG.Open.ordTwistedF4]
    ring
  · right; right; left
    rw [CFSG.RankThree.PartOne.S12K.card_of_reeTitsModel_Tits hT, CFSG.Open.ordTits]
    norm_num
  · right; right; right; left
    refine ⟨n, hn, ?_⟩
    rw [Nat.card_congr e.toEquiv,
      CFSG.RankThree.PartTwo.Sec19.Step1911Proof.card_projSp_two (by omega), pow_mul]
  · right; right; right; right; right
    obtain ⟨e⟩ := hA
    rw [Nat.card_congr e.toEquiv, Res4Three419.card_alternatingGroup_six]
    norm_num

end Types

theorem g2_ne {q : ℕ} (hq : 2 ≤ q) : (q ^ 6 - 1) * (q ^ 2 - 1) ≠ (q ^ 6) ^ 2 - 1 := by
  intro h
  obtain ⟨a, ha⟩ : ∃ a, a = q ^ 2 := ⟨_, rfl⟩
  have ha4 : 4 ≤ a := by
    rw [ha]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
  have e1 : q ^ 6 = a ^ 3 := by rw [ha]; ring
  rw [e1, ← ha] at h
  have h1 : 1 ≤ a ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ (a ^ 3) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ a := by omega
  zify [h1, h2, h3] at h
  have ha' : (4 : ℤ) ≤ a := by exact_mod_cast ha4
  have h4 : ((a : ℤ) ^ 3 - 1) * ((a : ℤ) - 1) < ((a : ℤ) ^ 3) ^ 2 - 1 := by
    have : ((a : ℤ) ^ 3) ^ 2 = (a : ℤ) ^ 6 := by ring
    rw [this]
    have h5 : (a : ℤ) ^ 4 ≤ (a : ℤ) ^ 6 - 2 := by
      have : (a : ℤ) ^ 6 = (a : ℤ) ^ 4 * (a : ℤ) ^ 2 := by ring
      have h6 : (16 : ℤ) ≤ (a : ℤ) ^ 2 := by nlinarith
      have h7 : (0 : ℤ) < (a : ℤ) ^ 4 := by positivity
      nlinarith
    have h8 : ((a : ℤ) ^ 3 - 1) * ((a : ℤ) - 1) ≤ (a : ℤ) ^ 4 := by
      have : (0 : ℤ) ≤ (a : ℤ) ^ 3 - 1 := by
        have : (1 : ℤ) ≤ (a : ℤ) ^ 3 := one_le_pow₀ (by linarith)
        linarith
      have h9 : (a : ℤ) ^ 3 - 1 ≤ (a : ℤ) ^ 3 := by linarith
      have h10 : (a : ℤ) - 1 ≤ (a : ℤ) := by linarith
      calc ((a : ℤ) ^ 3 - 1) * ((a : ℤ) - 1) ≤ (a : ℤ) ^ 3 * (a : ℤ) := by
            apply mul_le_mul h9 h10 (by linarith) (by positivity)
        _ = (a : ℤ) ^ 4 := by ring
    linarith
  linarith

theorem f4_ne {q : ℕ} (hq : 2 ≤ q) :
    (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1) ≠ (q ^ 12) ^ 2 - 1 := by
  intro h
  have h1 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ (q ^ 12) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  have h3 : 1 ≤ q := by omega
  have hq' : (2 : ℤ) ≤ q := by exact_mod_cast hq
  zify [h1, h2, h3] at h
  have h5 : ((q : ℤ) ^ 6 + 1) * ((q : ℤ) ^ 4 - 1) * ((q : ℤ) ^ 3 + 1) * ((q : ℤ) - 1) <
      ((q : ℤ) ^ 12) ^ 2 - 1 := by
    have a1 : (q : ℤ) ^ 6 + 1 ≤ (q : ℤ) ^ 7 := by
      have : (q : ℤ) ^ 7 = (q : ℤ) ^ 6 * q := by ring
      have : (1 : ℤ) ≤ (q : ℤ) ^ 6 := one_le_pow₀ (by linarith)
      nlinarith
    have a2 : (q : ℤ) ^ 4 - 1 ≤ (q : ℤ) ^ 4 := by linarith
    have a3 : (q : ℤ) ^ 3 + 1 ≤ (q : ℤ) ^ 4 := by
      have : (q : ℤ) ^ 4 = (q : ℤ) ^ 3 * q := by ring
      have : (1 : ℤ) ≤ (q : ℤ) ^ 3 := one_le_pow₀ (by linarith)
      nlinarith
    have a4 : (q : ℤ) - 1 ≤ (q : ℤ) := by linarith
    have p1 : (0 : ℤ) ≤ (q : ℤ) ^ 6 + 1 := by positivity
    have p2 : (0 : ℤ) ≤ (q : ℤ) ^ 4 - 1 := by
      have : (1 : ℤ) ≤ (q : ℤ) ^ 4 := one_le_pow₀ (by linarith)
      linarith
    have p3 : (0 : ℤ) ≤ (q : ℤ) ^ 3 + 1 := by positivity
    have p4 : (0 : ℤ) ≤ (q : ℤ) - 1 := by linarith
    have b : ((q : ℤ) ^ 6 + 1) * ((q : ℤ) ^ 4 - 1) * ((q : ℤ) ^ 3 + 1) * ((q : ℤ) - 1) ≤
        (q : ℤ) ^ 7 * (q : ℤ) ^ 4 * (q : ℤ) ^ 4 * (q : ℤ) := by
      gcongr
    have c : (q : ℤ) ^ 7 * (q : ℤ) ^ 4 * (q : ℤ) ^ 4 * (q : ℤ) = (q : ℤ) ^ 16 := by ring
    have d : (q : ℤ) ^ 16 < ((q : ℤ) ^ 12) ^ 2 - 1 := by
      have e : ((q : ℤ) ^ 12) ^ 2 = (q : ℤ) ^ 24 := by ring
      have f : (q : ℤ) ^ 24 = (q : ℤ) ^ 16 * (q : ℤ) ^ 8 := by ring
      have g : (4 : ℤ) ≤ (q : ℤ) ^ 8 := by
        have : (2 : ℤ) ^ 8 ≤ (q : ℤ) ^ 8 := pow_le_pow_left₀ (by norm_num) hq' 8
        linarith
      have g' : (0 : ℤ) < (q : ℤ) ^ 16 := by positivity
      rw [e, f]
      nlinarith
    linarith
  linarith

theorem sp4_ne {q : ℕ} (hq : 2 ≤ q) : (q ^ 2 - 1) * (q ^ 4 - 1) ≠ (q ^ 4) ^ 2 - 1 := by
  intro h
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ (q ^ 4) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  have hq' : (2 : ℤ) ≤ q := by exact_mod_cast hq
  zify [h1, h2, h3] at h
  have h4 : (4 : ℤ) ≤ (q : ℤ) ^ 2 := by nlinarith
  have h5 : (q : ℤ) ^ 4 = ((q : ℤ) ^ 2) ^ 2 := by ring
  have h6 : (0 : ℤ) < (q : ℤ) ^ 4 := by positivity
  have h8 : ((q : ℤ) ^ 4) ^ 2 = (q : ℤ) ^ 8 := by ring
  have h9 : (q : ℤ) ^ 8 = (q : ℤ) ^ 6 * (q : ℤ) ^ 2 := by ring
  have h10 : ((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 4 - 1) < (q : ℤ) ^ 6 := by
    have : ((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 4 - 1) < (q : ℤ) ^ 2 * (q : ℤ) ^ 4 := by nlinarith
    calc _ < (q : ℤ) ^ 2 * (q : ℤ) ^ 4 := this
      _ = (q : ℤ) ^ 6 := by ring
  have h11 : (0 : ℤ) < (q : ℤ) ^ 6 := by positivity
  rw [h8, h9] at h
  nlinarith


theorem card_ne_sl2_general {K : Type} [Group K] (h : IsType419 K) {m : ℕ} (hm : 1 ≤ m) :
    Nat.card K ≠ 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
  intro hK
  have hodd : Odd ((2 ^ m) ^ 2 - 1) := odd_two_pow_pow_sub_one hm (by norm_num)
  rcases card_isType419_explicit h with ⟨n, hn, hc⟩ | ⟨n, hn, hc⟩ | hc | ⟨n, hn, hc⟩ | hc | hc
  · have hq : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hu : Odd (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1)) :=
      (odd_two_pow_pow_sub_one (by omega) (by norm_num)).mul
        (odd_two_pow_pow_sub_one (by omega) (by norm_num))
    have hc' : Nat.card K = 2 ^ (n * 6) * (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1)) := by
      rw [hc, pow_mul]
    obtain ⟨h1, h2⟩ := eq_of_two_pow_mul_odd hu hodd (hc'.symm.trans hK)
    subst h1
    rw [pow_mul] at h2
    exact g2_ne hq h2
  · have hq : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h1' : Odd (2 ^ n - 1) := by
      simpa using odd_two_pow_pow_sub_one (j := 1) hn le_rfl
    have hu : Odd (((2 ^ n) ^ 6 + 1) * ((2 ^ n) ^ 4 - 1) * ((2 ^ n) ^ 3 + 1) * (2 ^ n - 1)) :=
      (((odd_two_pow_pow_add_one hn (by norm_num)).mul
        (odd_two_pow_pow_sub_one hn (by norm_num))).mul
          (odd_two_pow_pow_add_one hn (by norm_num))).mul h1'
    have hc' : Nat.card K = 2 ^ (n * 12) *
        (((2 ^ n) ^ 6 + 1) * ((2 ^ n) ^ 4 - 1) * ((2 ^ n) ^ 3 + 1) * (2 ^ n - 1)) := by
      rw [hc, pow_mul]
    obtain ⟨h1, h2⟩ := eq_of_two_pow_mul_odd hu hodd (hc'.symm.trans hK)
    subst h1
    rw [pow_mul] at h2
    exact f4_ne hq h2
  · obtain ⟨rfl, h3⟩ := eq_of_two_pow_mul_odd (by decide) hodd (hc.symm.trans hK)
    norm_num at h3
  · have hq : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hu : Odd (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1)) :=
      (odd_two_pow_pow_sub_one (by omega) (by norm_num)).mul
        (odd_two_pow_pow_sub_one (by omega) (by norm_num))
    have hc' : Nat.card K = 2 ^ (n * 4) * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1)) := by
      rw [hc, pow_mul]
    obtain ⟨h1, h2⟩ := eq_of_two_pow_mul_odd hu hodd (hc'.symm.trans hK)
    subst h1
    rw [pow_mul] at h2
    exact sp4_ne hq h2
  · obtain ⟨rfl, h3⟩ := eq_of_two_pow_mul_odd (by decide) hodd (hc.symm.trans hK)
    norm_num at h3
  · obtain ⟨rfl, h3⟩ := eq_of_two_pow_mul_odd (by decide) hodd (hc.symm.trans hK)
    norm_num at h3

end CFSG.RankThree.PartTwo.Sec4.Item419Res3
