module

public import CFSG.RankThree.GF2n.Smith81.InspKFacts
import CFSG.RankThree.GF2n.Smith81.InspLinCore

public section

namespace CFSG.RankThree.GF2n.Smith81.Insp

open CFSG CFSG.Blueprint CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Orders
open CFSG.SeitzReduction.F4Pilot (ordSL)

theorem linWindow_two {m f N : ℕ} {Z : ℕ → Prop} (hf : 2 ≤ f) (hpr : Profile m (f * N) Z)
    (hlo : 2 ^ (6 * f) ∣ m)
    (hup : m.factorization 2 ≤ 6 * f + 2 * f.factorization 2 + 2) :
    6 ≤ N ∧ N ≤ 8 := by
  have hf0 : 0 < f := by omega
  have hlo' : 6 * f ≤ f * N := le_of_two_pow_dvd_of_profile hpr hlo
  have hup' : f * N ≤ 6 * f + 2 * f.factorization 2 + 2 := by
    rwa [factorization_two_of_profile hpr] at hup
  have hv : f.factorization 2 < f := factorization_two_lt f (by omega)
  refine ⟨?_, ?_⟩
  · have h : f * 6 ≤ f * N := by rwa [mul_comm f 6]
    exact Nat.le_of_mul_le_mul_left h hf0
  · by_contra hN
    push Not at hN
    have h9 : f * 9 ≤ f * N := Nat.mul_le_mul_left f (by omega)
    omega

theorem linWindow_three {m f N : ℕ} {Z : ℕ → Prop} (hf : 2 ≤ f) (hpr : Profile m (f * N) Z)
    (hlo : 2 ^ (10 * f) ∣ m)
    (hup : m.factorization 2 ≤ 10 * f + 2 * f.factorization 2 + 1) :
    10 ≤ N ∧ N ≤ 11 := by
  have hf0 : 0 < f := by omega
  have hlo' : 10 * f ≤ f * N := le_of_two_pow_dvd_of_profile hpr hlo
  have hup' : f * N ≤ 10 * f + 2 * f.factorization 2 + 1 := by
    rwa [factorization_two_of_profile hpr] at hup
  have hv : f.factorization 2 < f := factorization_two_lt f (by omega)
  refine ⟨?_, ?_⟩
  · have h : f * 10 ≤ f * N := by rwa [mul_comm f 10]
    exact Nat.le_of_mul_le_mul_left h hf0
  · by_contra hN
    push Not at hN
    have h12 : f * 12 ≤ f * N := Nat.mul_le_mul_left f (by omega)
    omega

theorem psl_eq_four_of_linWindow {k : ℕ} (hk : 3 ≤ k)
    (hlo : 6 ≤ (k - 1) * (k - 1 + 1) / 2)
    (hhi : (k - 1) * (k - 1 + 1) / 2 ≤ 8) : k = 4 := by
  have hk1 : 1 ≤ k := by omega
  have hev : 2 * ((k - 1) * (k - 1 + 1) / 2) = (k - 1) * (k - 1 + 1) :=
    Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self (k - 1))
  have hk5 : k ≤ 5 := by
    by_contra h
    push Not at h
    have h6 : 6 ≤ k := by omega
    have h1 : 30 ≤ (k - 1) * k := by
      have := Nat.mul_le_mul (show 5 ≤ k - 1 by omega) h6
      simpa using this
    have h2 : (k - 1) * (k - 1 + 1) ≤ 16 := by omega
    rw [Nat.sub_add_cancel hk1] at h2
    omega
  interval_cases k
  · have h3 : (3 - 1) * (3 - 1 + 1) / 2 = 3 := by norm_num
    omega
  · rfl
  · have h5 : (5 - 1) * (5 - 1 + 1) / 2 = 10 := by norm_num
    omega

theorem psl_eq_five_of_linWindow {k : ℕ} (hk : 3 ≤ k)
    (hlo : 10 ≤ (k - 1) * (k - 1 + 1) / 2)
    (hhi : (k - 1) * (k - 1 + 1) / 2 ≤ 11) : k = 5 := by
  have hk1 : 1 ≤ k := by omega
  have hev : 2 * ((k - 1) * (k - 1 + 1) / 2) = (k - 1) * (k - 1 + 1) :=
    Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self (k - 1))
  have hk6 : k ≤ 6 := by
    by_contra h
    push Not at h
    have h7 : 7 ≤ k := by omega
    have h1 : 42 ≤ (k - 1) * k := by
      have := Nat.mul_le_mul (show 6 ≤ k - 1 by omega) h7
      simpa using this
    have h2 : (k - 1) * (k - 1 + 1) ≤ 22 := by omega
    rw [Nat.sub_add_cancel hk1] at h2
    omega
  interval_cases k
  · have h3 : (3 - 1) * (3 - 1 + 1) / 2 = 3 := by norm_num
    omega
  · have h6 : (4 - 1) * (4 - 1 + 1) / 2 = 6 := by norm_num
    omega
  · rfl
  · have h15 : (6 - 1) * (6 - 1 + 1) / 2 = 15 := by norm_num
    omega

section Tags


theorem exists_profile_of_exceptional {Y : Type} [Group Y] [Finite Y] {t : StatedLieTag}
    {f : ℕ} (hf : 1 ≤ f)
    (ht : t = .trialityD4 ∨ t = .F4 ∨ t = .E6 ∨ t = .twistedE6 ∨ t = .E7 ∨ t = .E8)
    (hL : LieModel Y t 0 2 f) :
    ∃ N : ℕ, 12 ≤ N ∧ ∃ Z : ℕ → Prop, Profile (Nat.card Y) (f * N) Z := by
  have hcard := card_chevalleyExceptionalModel_two (hL.chevalleyExceptionalModel (by
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> decide))
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨12, by norm_num, zD4 f, ?_⟩
    rw [hcard]
    exact profile_ordTrialityD4 hf
  · refine ⟨24, by norm_num, zF4 f, ?_⟩
    rw [hcard]
    exact profile_ordF4 hf
  · refine ⟨36, by norm_num, zE6 f, ?_⟩
    rw [hcard]
    exact profile_ordE6 hf
  · refine ⟨36, by norm_num, z2E6 f, ?_⟩
    rw [hcard]
    exact profile_ordTwistedE6 hf
  · refine ⟨63, by norm_num, zE7 f, ?_⟩
    rw [hcard]
    exact profile_ordE7 hf
  · refine ⟨120, by norm_num, zE8 f, ?_⟩
    rw [hcard]
    exact profile_ordE8 hf

theorem linCoreTwo {Y : Type} [Group Y] [Finite Y] {t : StatedLieTag} {k f : ℕ} (hf : 2 ≤ f)
    (htag : TimmesfeldTag t k f) (hL : LieModel Y t k 2 f) (hlo : 2 ^ (6 * f) ∣ Nat.card Y)
    (hup : (Nat.card Y).factorization 2 ≤ 6 * f + 2 * f.factorization 2 + 2) :
    (t = .PSL ∧ k = 4) ∨ (t = .G2 ∧ k = 0) := by
  have hf1 : 1 ≤ f := by omega
  rcases htag with ⟨rfl, hk⟩ | ⟨rfl, hk⟩ | ⟨ht, hk⟩ | ⟨rfl, rfl, -⟩ | ⟨rfl, ht⟩
  ·
    have hcard := (card_statedClassicalModel_two (hL.statedClassicalModel (by decide))).1 rfl
    have hpr : Profile (Nat.card Y) (f * ((k - 1) * (k - 1 + 1) / 2)) (zA (k - 1) f) := by
      rw [hcard]
      exact profile_ordA (by omega) hf1
    obtain ⟨hloN, hhiN⟩ := linWindow_two hf hpr hlo hup
    exact Or.inl ⟨rfl, psl_eq_four_of_linWindow hk hloN hhiN⟩
  ·
    exfalso
    have hcard := (card_statedClassicalModel_two (hL.statedClassicalModel (by decide))).2.2.1 rfl
    have hpr : Profile (Nat.card Y) (f * (k * k)) (zBC k f) := by
      rw [hcard]
      exact profile_ordBC hf1
    obtain ⟨-, hhiN⟩ := linWindow_two hf hpr hlo hup
    have h9 : 3 * 3 ≤ k * k := Nat.mul_le_mul hk hk
    omega
  ·
    exfalso
    rcases ht with rfl | rfl
    · have hcard :=
        (card_statedClassicalModel_two (hL.statedClassicalModel (by decide))).2.2.2.1 rfl
      have hpr : Profile (Nat.card Y) (f * (k * (k - 1))) (zD k f) := by
        rw [hcard]
        exact profile_ordD (by omega) hf1
      obtain ⟨-, hhiN⟩ := linWindow_two hf hpr hlo hup
      have h12 : 4 * 3 ≤ k * (k - 1) := Nat.mul_le_mul hk (by omega)
      omega
    · have hcard :=
        (card_statedClassicalModel_two (hL.statedClassicalModel (by decide))).2.2.2.2 rfl
      have hpr : Profile (Nat.card Y) (f * (k * (k - 1))) (z2D k f) := by
        rw [hcard]
        exact profile_ordTwistedD (by omega) hf1
      obtain ⟨-, hhiN⟩ := linWindow_two hf hpr hlo hup
      have h12 : 4 * 3 ≤ k * (k - 1) := Nat.mul_le_mul hk (by omega)
      omega
  ·
    exact Or.inr ⟨rfl, rfl⟩
  ·
    exfalso
    obtain ⟨N, hN, Z, hpr⟩ := exists_profile_of_exceptional hf1 ht hL
    obtain ⟨-, hhiN⟩ := linWindow_two hf hpr hlo hup
    omega

theorem linCoreThree {Y : Type} [Group Y] [Finite Y] {t : StatedLieTag} {k f : ℕ} (hf : 2 ≤ f)
    (htag : TimmesfeldTag t k f) (hL : LieModel Y t k 2 f) (hlo : 2 ^ (10 * f) ∣ Nat.card Y)
    (hup : (Nat.card Y).factorization 2 ≤ 10 * f + 2 * f.factorization 2 + 1) :
    t = .PSL ∧ k = 5 := by
  have hf1 : 1 ≤ f := by omega
  rcases htag with ⟨rfl, hk⟩ | ⟨rfl, hk⟩ | ⟨ht, hk⟩ | ⟨rfl, rfl, -⟩ | ⟨rfl, ht⟩
  ·
    have hcard := (card_statedClassicalModel_two (hL.statedClassicalModel (by decide))).1 rfl
    have hpr : Profile (Nat.card Y) (f * ((k - 1) * (k - 1 + 1) / 2)) (zA (k - 1) f) := by
      rw [hcard]
      exact profile_ordA (by omega) hf1
    obtain ⟨hloN, hhiN⟩ := linWindow_three hf hpr hlo hup
    exact ⟨rfl, psl_eq_five_of_linWindow hk hloN hhiN⟩
  ·
    exfalso
    have hcard := (card_statedClassicalModel_two (hL.statedClassicalModel (by decide))).2.2.1 rfl
    have hpr : Profile (Nat.card Y) (f * (k * k)) (zBC k f) := by
      rw [hcard]
      exact profile_ordBC hf1
    obtain ⟨hloN, hhiN⟩ := linWindow_three hf hpr hlo hup
    rcases Nat.lt_or_ge k 4 with h4 | h4 <;>
      [interval_cases k <;> omega; nlinarith [Nat.mul_le_mul h4 h4]]
  ·
    exfalso
    rcases ht with rfl | rfl
    · have hcard :=
        (card_statedClassicalModel_two (hL.statedClassicalModel (by decide))).2.2.2.1 rfl
      have hpr : Profile (Nat.card Y) (f * (k * (k - 1))) (zD k f) := by
        rw [hcard]
        exact profile_ordD (by omega) hf1
      obtain ⟨-, hhiN⟩ := linWindow_three hf hpr hlo hup
      have h12 : 4 * 3 ≤ k * (k - 1) := Nat.mul_le_mul hk (by omega)
      omega
    · have hcard :=
        (card_statedClassicalModel_two (hL.statedClassicalModel (by decide))).2.2.2.2 rfl
      have hpr : Profile (Nat.card Y) (f * (k * (k - 1))) (z2D k f) := by
        rw [hcard]
        exact profile_ordTwistedD (by omega) hf1
      obtain ⟨-, hhiN⟩ := linWindow_three hf hpr hlo hup
      have h12 : 4 * 3 ≤ k * (k - 1) := Nat.mul_le_mul hk (by omega)
      omega
  ·
    exfalso
    have hcard := card_chevalleyExceptionalModel_two (hL.chevalleyExceptionalModel (by decide))
    have hpr : Profile (Nat.card Y) (f * 6) (zG2 f) := by
      rw [hcard]
      exact profile_ordG2 hf1
    obtain ⟨hloN, -⟩ := linWindow_three hf hpr hlo hup
    omega
  ·
    exfalso
    obtain ⟨N, hN, Z, hpr⟩ := exists_profile_of_exceptional hf1 ht hL
    obtain ⟨-, hhiN⟩ := linWindow_three hf hpr hlo hup
    omega

end Tags

end CFSG.RankThree.GF2n.Smith81.Insp
