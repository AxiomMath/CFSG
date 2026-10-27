module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3A314Model

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def TargetCard (N : ℕ) : Prop :=
  N = 7560 ∨ N = 7800 ∨ N = 175560 ∨
    ∃ p : ℕ, p.Prime ∧ 11 ≤ p ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧ N = p * (p ^ 2 - 1) / 2

theorem psl2_mod_eight {p : ℕ} (h8 : p % 8 = 3 ∨ p % 8 = 5) :
    p * (p ^ 2 - 1) / 2 % 8 = 4 := by
  have h16 : p % 16 = 3 ∨ p % 16 = 5 ∨ p % 16 = 11 ∨ p % 16 = 13 := by omega
  have hsq : p ^ 2 % 16 = 9 := by
    rw [Nat.pow_mod]
    rcases h16 with h | h | h | h <;> rw [h]
  have hp1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
  generalize p ^ 2 = t at hsq hp1
  have h2 : 2 ∣ t - 1 := by omega
  rw [Nat.mul_div_assoc _ h2, Nat.mul_mod]
  have h3 : (t - 1) / 2 % 8 = 4 := by omega
  rw [h3]
  rcases h8 with h | h <;> rw [h]

theorem psl2_ge {p : ℕ} (hp : 11 ≤ p) : 660 ≤ p * (p ^ 2 - 1) / 2 := by
  have h1 : 120 ≤ p ^ 2 - 1 := by
    have : 121 ≤ p ^ 2 := by nlinarith
    omega
  have : 1320 ≤ p * (p ^ 2 - 1) := by nlinarith
  omega

theorem psl2_gt {p : ℕ} (hp : 18 ≤ p) : 2520 < p * (p ^ 2 - 1) / 2 := by
  have h1 : 323 ≤ p ^ 2 - 1 := by
    have : 324 ≤ p ^ 2 := by nlinarith
    omega
  have : 5814 ≤ p * (p ^ 2 - 1) := by nlinarith
  omega

theorem not_sixteen_dvd {N : ℕ} (h : TargetCard N) : ¬ 16 ∣ N := by
  rcases h with rfl | rfl | rfl | ⟨p, -, -, h8, rfl⟩
  · norm_num
  · norm_num
  · norm_num
  · have := psl2_mod_eight h8
    omega

theorem le_of_targetCard {N : ℕ} (h : TargetCard N) : 660 ≤ N := by
  rcases h with rfl | rfl | rfl | ⟨p, -, hp, -, rfl⟩
  · norm_num
  · norm_num
  · norm_num
  · exact psl2_ge hp

theorem not_targetCard_of_lt {N : ℕ} (hN : N < 660) : ¬ TargetCard N :=
  fun h => absurd (le_of_targetCard h) (by omega)

theorem not_targetCard_of_dvd {N : ℕ} (hN : 16 ∣ N) : ¬ TargetCard N :=
  fun h => not_sixteen_dvd h hN

theorem not_targetCard_of_le {N : ℕ} (hN : N ≤ 2520) (h660 : N ≠ 660) (h1092 : N ≠ 1092)
    (h2448 : N ≠ 2448) : ¬ TargetCard N := by
  rintro (rfl | rfl | rfl | ⟨p, hpr, hp, -, rfl⟩)
  · omega
  · omega
  · omega
  · rcases Nat.lt_or_ge p 18 with h18 | h18
    · interval_cases p <;> revert hpr h660 h1092 h2448 <;> norm_num
    · exact absurd (psl2_gt h18) (by omega)

theorem not_targetCard_1080 : ¬ TargetCard 1080 :=
  not_targetCard_of_le (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem not_targetCard_2520 : ¬ TargetCard 2520 :=
  not_targetCard_of_le (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem not_targetCard_sl2 (n : ℕ) : ¬ TargetCard (2 ^ n * (4 ^ n - 1)) := by
  rcases Nat.lt_or_ge n 4 with hn | hn
  · interval_cases n <;> exact not_targetCard_of_lt (by norm_num)
  · refine not_targetCard_of_dvd (Dvd.dvd.mul_right ?_ _)
    exact (show (16 : ℕ) = 2 ^ 4 by norm_num) ▸ pow_dvd_pow 2 hn

theorem target_props {Y : Type} [Group Y] [Finite Y]
    (h : IsHat Y ↥(alternatingGroup (Fin 7)) ∨ IsPSL 2 5 2 Y ∨
      (∃ p : ℕ, p.Prime ∧ 11 ≤ p ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧ IsPSL 2 p 1 Y) ∨
      IsSporadic .J1 Y) :
    TargetCard (Nat.card Y) ∧ (IsHat Y ↥(alternatingGroup (Fin 7)) ∨ IsSimpleGroup Y) := by
  rcases h with h | h | ⟨p, hp, h11, h8, h⟩ | h
  · refine ⟨Or.inl ?_, Or.inl h⟩
    obtain ⟨-, hc, ⟨e⟩⟩ := h
    rw [Lin2.OddRank.card_of_cover_alt (m := 7) (by norm_num) hc e]
    decide
  · refine ⟨Or.inr (Or.inl ?_), Or.inr (CFSG.LieType.Simplicity.fam_PSL_simplicity Y 2 5 2 h).2⟩
    rw [Lin2.OddRank.card_of_openPSL (by norm_num) h]
    decide
  · obtain ⟨hs, -, hc⟩ := A5.G3.modelFacts_part3 hp (by omega) h
    exact ⟨Or.inr (Or.inr (Or.inr ⟨p, hp, h11, h8, hc⟩)), Or.inr hs⟩
  · obtain ⟨e⟩ := h
    refine ⟨Or.inr (Or.inr (Or.inl ?_)), Or.inr ?_⟩
    · rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.J1.card_J1
    · exact @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.J1.isSimpleGroup_J1 e

end CFSG.Quasithin.Vol2.Ch10.SecF.C10KH
