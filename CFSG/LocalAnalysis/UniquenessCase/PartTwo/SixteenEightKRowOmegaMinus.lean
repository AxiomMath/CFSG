module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8RowBase
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKBound
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKMult
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKOmegaTwo
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSmall
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSmallShapes

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem s16k_false_of_natOmegaMinus (h : S16gRowCtx D V₀ V L hV)
    (hGA : CFSG.Open.GriessAllModelsStatement) {n a : ℕ} (ha : a = 1 ∨ a = 2)
    (hΩ : IsOmegaMinus ↥(lBar V₀ V hV L) n a)
    (hN : NatOmegaMinus (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) n a) : False := by
  obtain ⟨hev, K, hF, hFin, b, c, hK, hirr, hR⟩ := hN
  letI := hF
  letI := hFin
  haveI : CharP K 2 := s16k_charP_two_of_card (a := a) (by omega) hK
  generalize hm : n / 2 = m at hR
  have hKab : Nat.card K = 2 ∨ Nat.card K = 4 := by
    rcases ha with rfl | rfl
    · left; simpa using hK
    · right; rw [hK]; norm_num
  have hm2 : 2 ≤ m := by
    by_cases hm1 : m ≤ 1
    · rcases ha with rfl | rfl
      · have h4 := s16k_four_le_of_isOmegaMinus h.quasi hΩ
        have h2n := Nat.two_mul_div_two_of_even hev
        omega
      · have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
        exact absurd h.quasi (s16g_not_isQuasisimple_of_realizes_comm
          (s16k_comm_statedOmegaMinus_of_le_one_four hK4 hirr hm1) hR)
    · omega
  haveI : Nonempty (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
  obtain ⟨p, hpσ⟩ := h.std.hx.sig_nonempty
  have hp : p.Prime := (D.sig_prime p hpσ).1
  have hp2 : p ≠ 2 := (D.sig_prime p hpσ).2
  have hrk3 := h.three_le_pRank hpσ
  obtain ⟨ρ, hρ, hρN⟩ := h.exists_embedding hR
  have hpodd : 3 ≤ p := by have := hp.two_le; omega
  have hA : ¬ p ∣ Nat.card (RingAut K) := by
    rw [s16k_card_ringAut_of_card (a := a) hK]
    intro hd
    have ha1 : 1 ≤ a := by omega
    have hle := Nat.le_of_dvd ha1 hd
    have ha2 : a ≤ 2 := by rcases ha with rfl | rfl <;> norm_num
    omega
  have hdiv : Nat.card Kˣ ∣ Nat.card K ^ 2 - 1 := by
    rw [s16k_card_units_of_card (a := a) hK, hK]
    rcases ha with rfl | rfl <;> norm_num
  by_cases hm3 : 3 ≤ m
  · by_cases hpq : p ∣ Nat.card K ^ 2 - 1
    · by_cases hm4 : 4 ≤ m
      · rcases ha with rfl | rfl
        · have hK2 : Nat.card K = 2 := by simpa using hK
          have hp_eq : p = 3 := by
            have h3 : Nat.card K ^ 2 - 1 = 3 := by rw [hK2]; norm_num
            exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (by rw [← h3]; exact hpq)
          exact h.false_of_fixNc hR hpσ (by
            rw [hp_eq]
            exact s16k_fixNc_statedOmegaMinus_two_two hK2 hm4 hirr)
        · have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
          exact h.false_of_fixNc hR hpσ
            (s16g_fixNc_statedOmegaMinus_two (by norm_num [hK4]) hm4 hirr hp hp2 hpq)
      · have hm_eq : m = 3 := by omega
        have hn6 : n = 6 := by
          have h2n := Nat.two_mul_div_two_of_even hev
          omega
        rw [hn6] at hΩ
        have hrk : CFSG.Open.pRank p (Mbar D.M V₀ V hV) ≤ 3 := by
          rcases ha with rfl | rfl
          · have hK2 : Nat.card K = 2 := by simpa using hK
            have hp_eq : p = 3 := by
              have h3 : Nat.card K ^ 2 - 1 = 3 := by rw [hK2]; norm_num
              exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (by rw [← h3]; exact hpq)
            have h1 : ¬ p ∣ Nat.card K ^ 3 - 1 := by rw [hp_eq, hK2]; norm_num
            have hU : ¬ p ∣ Nat.card Kˣ := by
              rw [hp_eq, s16k_card_units_of_card (a := 1) (by rw [hK2]; norm_num)]
              norm_num
            exact s16k_pRank_le_statedOmegaMinus_three_six hirr hm_eq hp hp2 hpq h1 hA hU
              ρ hρ hρN
          · have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
            have hp35 : p = 3 ∨ p = 5 := by
              have h15 : Nat.card K ^ 2 - 1 = 15 := by rw [hK4]; norm_num
              have hd : p ∣ 3 * 5 := by
                rw [show (3 : ℕ) * 5 = 15 by norm_num, ← h15]
                exact hpq
              rcases hp.dvd_mul.1 hd with hd3 | hd5
              · left; exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hd3
              · right; exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 hd5
            rcases hp35 with hp_eq | hp_eq
            · have h1 : ¬ p ∣ Nat.card K ^ 3 + 1 := by rw [hp_eq, hK4]; norm_num
              have hU : Nat.card Kˣ = p := by
                rw [hp_eq, s16k_card_units_of_card (a := 2) (by rw [hK4]; norm_num)]
                norm_num
              exact s16k_pRank_le_statedOmegaMinus_three_four hirr hm_eq hp hp2 hpq h1 hA hU
                ρ hρ hρN
            · have h1 : ¬ p ∣ Nat.card K ^ 3 - 1 := by rw [hp_eq, hK4]; norm_num
              have hU : ¬ p ∣ Nat.card Kˣ := by
                rw [hp_eq, s16k_card_units_of_card (a := 2) (by rw [hK4]; norm_num)]
                norm_num
              exact s16k_pRank_le_statedOmegaMinus_three_six hirr hm_eq hp hp2 hpq h1 hA hU
                ρ hρ hρN
        rcases ha with rfl | rfl
        · have hK2 : Nat.card K = 2 := by simpa using hK
          have hp_eq : p = 3 := by
            have h3 : Nat.card K ^ 2 - 1 = 3 := by rw [hK2]; norm_num
            exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (by rw [← h3]; exact hpq)
          obtain ⟨hz, hmult⟩ := s16k_card_omegaMinus6_two hGA hΩ
          exact h.false_of_fixOrd hR hpσ (by rw [hz]; exact odd_one)
            (by rw [hmult, hp_eq]; norm_num) hrk
            (by rw [hp_eq, hm_eq]; exact s16k_fixOrd_statedOmegaMinus_three_two hK2 hirr)
        · have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
          obtain ⟨hz, hmult⟩ := s16k_trivial_omegaMinus6_four hGA hΩ
          exact h.false_of_fixOrd hR hpσ (by rw [hz]; exact odd_one)
            (by rw [hmult]; exact fun hd => hp.one_lt.ne' (Nat.dvd_one.1 hd)) hrk
            (by
              rw [hm_eq]
              exact s16g_fixOrd_statedOmegaMinus_three (by norm_num [hK4]) hirr hp hp2 hpq)
    · have hU : ¬ p ∣ Nat.card Kˣ := fun hd => hpq (hd.trans hdiv)
      exact h.false_of_fixNc hR hpσ
        (s16k_fixNc_statedOmegaMinus_of_pRank hm3 hirr hp hp2 hpq hA hU ρ hρ hρN hrk3)
  · have hm_eq : m = 2 := by omega
    have hrk := s16k_pRank_le_statedOmegaMinus_two hKab hirr hm_eq hp hp2 ρ hρ hρN
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
