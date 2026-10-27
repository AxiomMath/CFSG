module

public import CFSG.RankThree.PartOne.N143.Weyl613Small
public import CFSG.RankThree.PartOne.S12K.OrdRigid
public import CFSG.RankThree.PartOne.F106.ConvOrdBound
public import CFSG.RankThree.PartOne.N143.Statements

public section

namespace CFSG.RankThree.PartOne.F106

open CFSG.Open (ordA ordTwistedA)
open CFSG.Timmesfeld.Orders CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.N143
  CFSG.RankThree.PartOne.S12K

theorem tri_bounds {m f : ℕ} (hm : 5 ≤ m) (hf : 1 ≤ f) (hne : ¬ (m = 5 ∧ f = 1)) :
    20 ≤ f * (m * (m + 1) / 2) ∧ (f * (m * (m + 1) / 2) = 21 → m = 6 ∧ f = 1) := by
  have h2 := two_mul_tri m
  generalize m * (m + 1) / 2 = T at h2 ⊢
  have hT15 : 15 ≤ T := by nlinarith
  rcases Nat.lt_or_ge f 2 with hf1 | hf2
  · obtain rfl : f = 1 := by omega
    have hm6 : 6 ≤ m := by omega
    have hT21 : 21 ≤ T := by nlinarith
    refine ⟨by omega, fun h => ?_⟩
    have hT : T = 21 := by omega
    have : m = 6 := by
      rcases Nat.lt_or_ge m 7 with h7 | h7
      · omega
      · nlinarith
    exact ⟨this, rfl⟩
  · refine ⟨by nlinarith, fun h => ?_⟩
    nlinarith

theorem orth_bounds {k f : ℕ} (hf : 1 ≤ f) :
    20 ≤ f * ((k + 5) * (k + 4)) ∧ f * ((k + 5) * (k + 4)) ≠ 21 := by
  have h20 : 20 ≤ (k + 5) * (k + 4) := by nlinarith
  have hfm : (k + 5) * (k + 4) ≤ f * ((k + 5) * (k + 4)) := Nat.le_mul_of_pos_left _ hf
  refine ⟨le_trans h20 hfm, fun h => ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · omega
  · have h30 : 30 ≤ (k + 5) * (k + 4) := by nlinarith
    omega

theorem twoAdic_of_nonSmall {t : StatedLieTag} {n f : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (hns : ¬ SmallEvenParams t n f) :
    ∃ N r : ℕ, Odd r ∧ charTwoOrder t n f = 2 ^ N * r ∧ 20 ≤ N ∧
      charTwoOrder t n f ^ 4 ≤ (2 ^ N) ^ 11 ∧ (N = 21 → t = .PSU ∧ n = 7 ∧ f = 1) := by
  have hf : 1 ≤ f := hadm.2.1
  have hadm' := hadm.2.2
  have h2f : 2 ≤ 2 ^ f :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  cases t
  case PSL =>
    simp only [SmallEvenParams] at hns
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hm : 5 ≤ m := by omega
    have hne : ¬ (m = 5 ∧ f = 1) := by omega
    have e : charTwoOrder .PSL (m + 1) f = ordA m (2 ^ f) := by simp [charTwoOrder]
    obtain ⟨r, hr, hm'⟩ := (profile_ordA (n := m) (by omega) hf).two
    have hb : charTwoOrder .PSL (m + 1) f ^ 4 ≤ (2 ^ (f * (m * (m + 1) / 2))) ^ 11 := by
      rw [e]
      refine pow_four_le_of (ordA_le m (2 ^ f)) ?_
      have h2 := two_mul_tri m
      generalize m * (m + 1) / 2 = T at h2 ⊢
      nlinarith
    refine ⟨_, r, hr, e.trans hm', (tri_bounds hm hf hne).1, hb, fun h => ?_⟩
    obtain ⟨h6, h1⟩ := (tri_bounds hm hf hne).2 h
    omega
  case PSU =>
    simp only [SmallEvenParams] at hns
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hm : 5 ≤ m := by omega
    have hne : ¬ (m = 5 ∧ f = 1) := by omega
    have e : charTwoOrder .PSU (m + 1) f = ordTwistedA m (2 ^ f) := by simp [charTwoOrder]
    obtain ⟨r, hr, hm'⟩ := (profile_ordTwistedA (n := m) (by omega) hf).two
    have hb : charTwoOrder .PSU (m + 1) f ^ 4 ≤ (2 ^ (f * (m * (m + 1) / 2))) ^ 11 := by
      rw [e]
      refine pow_four_le_of (ordTwistedA_le m (2 ^ f) h2f) ?_
      have h2 := two_mul_tri m
      generalize m * (m + 1) / 2 = T at h2 ⊢
      nlinarith
    refine ⟨_, r, hr, e.trans hm', (tri_bounds hm hf hne).1, hb, fun h => ?_⟩
    obtain ⟨h6, h1⟩ := (tri_bounds hm hf hne).2 h
    exact ⟨rfl, by omega, h1⟩
  case PSp =>
    simp only [SmallEvenParams] at hns
    have hn : 5 ≤ n := by omega
    obtain ⟨r, hr, hm'⟩ := (profile_ordBC (n := n) hf).two
    have h25 : 25 ≤ f * (n * n) := by nlinarith
    have hb : charTwoOrder .PSp n f ^ 4 ≤ (2 ^ (f * (n * n))) ^ 11 :=
      pow_four_le_of (ordBC_le n (2 ^ f)) (by nlinarith)
    exact ⟨_, r, hr, hm', by omega, hb, fun h => by omega⟩
  case POmegaOdd => exact absurd rfl hadm'.2
  case POmegaPlus =>
    simp only [SmallEvenParams] at hns
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
    obtain ⟨r, hr, hm'⟩ := (profile_ordD (n := k + 5) (by omega) hf).two
    rw [show k + 5 - 1 = k + 4 by omega] at hm'
    obtain ⟨h1, h2⟩ := orth_bounds (k := k) hf
    have hb : charTwoOrder .POmegaPlus (k + 5) f ^ 4 ≤ (2 ^ (f * ((k + 5) * (k + 4)))) ^ 11 :=
      pow_four_le_of (ordD_le (k + 4) (2 ^ f)) (by nlinarith)
    exact ⟨_, r, hr, hm', h1, hb, fun h => absurd h h2⟩
  case POmegaMinus =>
    simp only [SmallEvenParams] at hns
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
    obtain ⟨r, hr, hm'⟩ := (profile_ordTwistedD (n := k + 5) (by omega) hf).two
    rw [show k + 5 - 1 = k + 4 by omega] at hm'
    obtain ⟨h1, h2⟩ := orth_bounds (k := k) hf
    have hb : charTwoOrder .POmegaMinus (k + 5) f ^ 4 ≤ (2 ^ (f * ((k + 5) * (k + 4)))) ^ 11 :=
      pow_four_le_of (ordTwistedD_le (k + 4) (2 ^ f) h2f) (by nlinarith)
    exact ⟨_, r, hr, hm', h1, hb, fun h => absurd h h2⟩
  case G2 => exact (hns (by simp [SmallEvenParams])).elim
  case F4 =>
    simp only [SmallEvenParams] at hns
    obtain ⟨r, hr, hm'⟩ := (profile_ordF4 (f := f) hf).two
    exact ⟨_, r, hr, hm', by omega, pow_four_le_of (ordF4_le (2 ^ f)) (by norm_num),
      fun h => by omega⟩
  case E6 =>
    obtain ⟨r, hr, hm'⟩ := (profile_ordE6 (f := f) hf).two
    exact ⟨_, r, hr, hm', by omega, pow_four_le_of (ordE6_le (2 ^ f)) (by norm_num),
      fun h => by omega⟩
  case E7 =>
    obtain ⟨r, hr, hm'⟩ := (profile_ordE7 (f := f) hf).two
    exact ⟨_, r, hr, hm', by omega, pow_four_le_of (ordE7_le (2 ^ f)) (by norm_num),
      fun h => by omega⟩
  case E8 =>
    obtain ⟨r, hr, hm'⟩ := (profile_ordE8 (f := f) hf).two
    exact ⟨_, r, hr, hm', by omega, pow_four_le_of (ordE8_le (2 ^ f)) (by norm_num),
      fun h => by omega⟩
  case twistedE6 =>
    obtain ⟨r, hr, hm'⟩ := (profile_ordTwistedE6 (f := f) hf).two
    exact ⟨_, r, hr, hm', by omega, pow_four_le_of (ordTwistedE6_le (2 ^ f) h2f) (by norm_num),
      fun h => by omega⟩
  case trialityD4 => exact (hns (by simp [SmallEvenParams])).elim
  case twistedB2 => exact (hns (by simp [SmallEvenParams])).elim
  case twistedG2 => exact absurd hadm'.2.1 (by norm_num)
  case twistedF4 => exact (hns (by simp [SmallEvenParams])).elim
  case Tits => exact (hns (by simp [SmallEvenParams])).elim

end CFSG.RankThree.PartOne.F106
