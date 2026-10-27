module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.Defs
public import CFSG.RankThree.PartOne.S12K.Rigidity
import CFSG.GH74.Orders.LieType

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)

private theorem k330c_six_sub_one (q : ℕ) :
    q ^ 6 - 1 = (q ^ 2 - 1) * (q ^ 4 + q ^ 2 + 1) := by
  rcases Nat.eq_zero_or_pos q with h | h
  · subst h; norm_num
  · have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ h
    have h6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ h
    zify [h1, h6]
    ring

private theorem k330c_three_dvd_sq_sub_one {q : ℕ} (h : ¬ 3 ∣ q) : 3 ∣ q ^ 2 - 1 := by
  have h0 : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; exact h (dvd_zero 3))
  have h1 : q ^ 2 % 3 = 1 := by
    have : q % 3 = 1 ∨ q % 3 = 2 := by omega
    rcases this with h | h <;> rw [Nat.pow_mod, h]
  have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ h0
  omega

private theorem k330c_three_dvd_four_add_sq_add_one {q : ℕ} (h : ¬ 3 ∣ q) :
    3 ∣ q ^ 4 + q ^ 2 + 1 := by
  obtain ⟨k, hk⟩ := k330c_three_dvd_sq_sub_one h
  have h0 : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; exact h (dvd_zero 3))
  have hq2 : q ^ 2 = 3 * k + 1 := by
    have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ h0
    omega
  refine ⟨3 * k ^ 2 + 3 * k + 1, ?_⟩
  rw [show q ^ 4 = (q ^ 2) ^ 2 by ring, hq2]
  ring

private theorem k330c_three_dvd_eight_add_four_add_one {q : ℕ} (h : ¬ 3 ∣ q) :
    3 ∣ q ^ 8 + q ^ 4 + 1 := by
  obtain ⟨k, hk⟩ := k330c_three_dvd_sq_sub_one h
  have h0 : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; exact h (dvd_zero 3))
  have hq2 : q ^ 2 = 3 * k + 1 := by
    have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ h0
    omega
  refine ⟨27 * k ^ 4 + 36 * k ^ 3 + 21 * k ^ 2 + 6 * k + 1, ?_⟩
  rw [show q ^ 8 = (q ^ 2) ^ 4 by ring, show q ^ 4 = (q ^ 2) ^ 2 by ring, hq2]
  ring

theorem k330c_27_dvd_ordG2 (q : ℕ) : 27 ∣ ordG2 q := by
  by_cases h3 : 3 ∣ q
  · obtain ⟨k, rfl⟩ := h3
    unfold ordG2
    exact (show 27 ∣ (3 * k) ^ 6 from ⟨27 * k ^ 6, by ring⟩).mul_right _ |>.mul_right _
  · have h1 : 3 ∣ q ^ 2 - 1 := k330c_three_dvd_sq_sub_one h3
    have h2 : 3 ∣ q ^ 4 + q ^ 2 + 1 := k330c_three_dvd_four_add_sq_add_one h3
    have h9 : 9 ∣ (q ^ 2 - 1) ^ 2 := by
      rw [pow_two]; exact mul_dvd_mul h1 h1
    have h27 : 27 ∣ (q ^ 2 - 1) ^ 2 * (q ^ 4 + q ^ 2 + 1) := by
      have := mul_dvd_mul h9 h2
      norm_num at this
      exact this
    have heq : ordG2 q = q ^ 6 * ((q ^ 2 - 1) ^ 2 * (q ^ 4 + q ^ 2 + 1)) := by
      rw [show ordG2 q = q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1) from rfl, k330c_six_sub_one]
      ring_nf
    rw [heq]
    exact h27.mul_left (q ^ 6)

theorem k330c_27_dvd_ordTrialityD4 (q : ℕ) : 27 ∣ ordTrialityD4 q := by
  by_cases h3 : 3 ∣ q
  · obtain ⟨k, rfl⟩ := h3
    unfold ordTrialityD4
    refine (show 27 ∣ (3 * k) ^ 12 from ⟨3 ^ 9 * k ^ 12, by ring⟩).mul_right _ |>.mul_right _
      |>.mul_right _
  · have h1 : 3 ∣ q ^ 2 - 1 := k330c_three_dvd_sq_sub_one h3
    have h8 : 3 ∣ q ^ 8 + q ^ 4 + 1 := k330c_three_dvd_eight_add_four_add_one h3
    have h6 : 3 ∣ q ^ 6 - 1 := by
      rw [k330c_six_sub_one]; exact h1.mul_right _
    have h27 : 27 ∣ (q ^ 2 - 1) * (q ^ 6 - 1) * (q ^ 8 + q ^ 4 + 1) := by
      have := mul_dvd_mul (mul_dvd_mul h1 h6) h8
      norm_num at this
      exact this
    have heq : ordTrialityD4 q =
        q ^ 12 * ((q ^ 2 - 1) * (q ^ 6 - 1) * (q ^ 8 + q ^ 4 + 1)) := by
      rw [show ordTrialityD4 q =
        q ^ 12 * (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1) from rfl]
      ring_nf
    rw [heq]
    exact h27.mul_left (q ^ 12)

theorem k330c_27_dvd_ordTits : 27 ∣ ordTits := by
  rw [ordTits]; norm_num

private theorem k330c_two_pow_mod_three {f : ℕ} (hf : Odd f) : 2 ^ f % 3 = 2 := by
  obtain ⟨k, rfl⟩ := hf
  have h4 : 2 ^ (2 * k) % 3 = 1 := by rw [pow_mul, Nat.pow_mod]; norm_num
  rw [pow_succ, Nat.mul_mod, h4]

private theorem k330c_three_dvd_add_one {q : ℕ} (h : q % 3 = 2) : 3 ∣ q + 1 := by
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, h]

private theorem k330c_three_dvd_sq_sub_self_add_one {q : ℕ} (h : q % 3 = 2) :
    3 ∣ q ^ 2 - q + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, q = 3 * k + 2 := by
    refine ⟨q / 3, ?_⟩
    have := Nat.div_add_mod q 3
    omega
  refine ⟨3 * k ^ 2 + 3 * k + 1, ?_⟩
  ring_nf
  omega

private theorem k330c_three_dvd_four_sub_one {q : ℕ} (h : q % 3 = 2) : 3 ∣ q ^ 4 - 1 := by
  have hq3 : ¬ 3 ∣ q := by rw [Nat.dvd_iff_mod_eq_zero]; omega
  have h1 : 3 ∣ q ^ 2 - 1 := k330c_three_dvd_sq_sub_one hq3
  have heq : q ^ 4 - 1 = (q ^ 2 - 1) * (q ^ 2 + 1) := by
    have h2 := Nat.sq_sub_sq (q ^ 2) 1
    rw [← pow_mul] at h2
    simpa [pow_two, mul_comm] using h2
  rw [heq]
  exact h1.mul_right _

private theorem k330c_nine_dvd_cube_add_one {q : ℕ} (h : q % 3 = 2) : 9 ∣ q ^ 3 + 1 := by
  have h1 : 3 ∣ q + 1 := k330c_three_dvd_add_one h
  have h2 : 3 ∣ q ^ 2 - q + 1 := k330c_three_dvd_sq_sub_self_add_one h
  have heq : q ^ 3 + 1 = (q + 1) * (q ^ 2 - q + 1) := by
    have h0 : 1 ≤ q := by omega
    have hle : q ≤ q ^ 2 := by
      calc q = q * 1 := (mul_one q).symm
        _ ≤ q * q := Nat.mul_le_mul_left q h0
        _ = q ^ 2 := (pow_two q).symm
    zify [h0, hle]
    ring
  rw [heq]
  have := mul_dvd_mul h1 h2
  norm_num at this
  exact this

theorem k330c_27_dvd_ordTwistedF4 {f : ℕ} (hf : Odd f) : 27 ∣ ordTwistedF4 (2 ^ f) := by
  have hq : (2 ^ f) % 3 = 2 := k330c_two_pow_mod_three hf
  have h4 : 3 ∣ (2 ^ f) ^ 4 - 1 := k330c_three_dvd_four_sub_one hq
  have h9 : 9 ∣ (2 ^ f) ^ 3 + 1 := k330c_nine_dvd_cube_add_one hq
  have h27 : 27 ∣ ((2 ^ f) ^ 4 - 1) * ((2 ^ f) ^ 3 + 1) := by
    have := mul_dvd_mul h4 h9
    norm_num at this
    exact this
  unfold ordTwistedF4
  have h := h27.mul_left ((2 ^ f) ^ 12 * ((2 ^ f) ^ 6 + 1)) |>.mul_right ((2 ^ f) - 1)
  simpa only [mul_assoc] using h


theorem excl_G2 {J : Type} [Group J] [Finite J] {p f : ℕ} (e : LieModel J .G2 0 p f) :
    Excl J := by
  refine Or.inl ?_
  have hmodel := CFSG.GH74.chevalleyExceptionalModel_of_lieModel (t := .G2) (by decide) e
  have hcard := (CFSG.Timmesfeld.card_chevalleyExceptionalModel_untwisted hmodel).1 rfl
  rw [Big27, hcard]
  exact k330c_27_dvd_ordG2 (p ^ f)

theorem excl_3D4 {J : Type} [Group J] [Finite J] {p f : ℕ}
    (e : LieModel J .trialityD4 0 p f) : Excl J := by
  refine Or.inl ?_
  by_cases hp2 : p = 2
  · subst hp2
    have hmodel := CFSG.GH74.chevalleyExceptionalModel_of_lieModel (t := .trialityD4) (by decide) e
    have hcard := CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hmodel
    rw [Big27, hcard]
    exact k330c_27_dvd_ordTrialityD4 (2 ^ f)
  · have hcard := CFSG.GH74.card_of_lieModel_trialityD4 hp2 e
    rw [Big27, hcard]
    exact k330c_27_dvd_ordTrialityD4 (p ^ f)

theorem excl_2F4 {J : Type} [Group J] [Finite J] {f : ℕ} (e : LieModel J .twistedF4 0 2 f) :
    Excl J := by
  rcases e with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, hmodel⟩ | ⟨-, h, -⟩
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · obtain ⟨-, -, -, -, hfodd, -⟩ := hmodel.1
    refine Or.inl ?_
    rw [Big27, CFSG.RankThree.PartOne.S12K.card_of_reeTitsModel_twistedF4 hmodel]
    exact k330c_27_dvd_ordTwistedF4 hfodd
  · exact absurd h (by decide)

theorem excl_Tits
    {J : Type} [Group J] [Finite J] (e : LieModel J .Tits 0 2 1) :
    Excl J := by
  rcases e with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, hmodel⟩ | ⟨-, h, -⟩
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · refine Or.inl ?_
    rw [Big27, CFSG.RankThree.PartOne.S12K.card_of_reeTitsModel_Tits hmodel]
    exact k330c_27_dvd_ordTits
  · exact absurd h (by decide)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg
