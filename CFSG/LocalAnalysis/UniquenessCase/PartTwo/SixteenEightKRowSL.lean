module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8RowBase
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Small
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8TwoSL
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKBound
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKMultSL3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem s16k_false_of_binaryNaturalSL (h : S16gRowCtx D V₀ V L hV)
    (hGA : CFSG.Open.GriessAllModelsStatement) {n a : ℕ} (ha : a = 1 ∨ a = 2)
    (hSL : IsSLn ↥(lBar V₀ V hV L) n a)
    (hN : BinaryNaturalSL (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) n a) : False := by
  obtain ⟨K, hF, hFin, hK, hR⟩ := hN
  letI := hF
  letI := hFin
  by_cases hn : n ≤ 1
  · exact s16g_not_isQuasisimple_of_realizes_comm
      (fun x _ y _ => s16g_mul_comm_of_card_le_one (by rw [Fintype.card_fin]; omega) x y) hR
      h.quasi
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨p, hpσ⟩ := h.std.hx.sig_nonempty
  have hp : p.Prime := (D.sig_prime p hpσ).1
  have hp2 : p ≠ 2 := (D.sig_prime p hpσ).2
  have hrk3 := h.three_le_pRank hpσ
  obtain ⟨ρ, hρ, hρN⟩ := h.exists_embedding hR
  have hA : ¬ p ∣ Nat.card (RingAut K) := by
    rw [s16k_card_ringAut_of_card hK]
    intro hdvd
    have hp2' : 2 ≤ p := hp.two_le
    have hle : p ≤ a := Nat.le_of_dvd (by rcases ha with h | h <;> omega) hdvd
    have hle2 : a ≤ 2 := by rcases ha with h | h <;> omega
    omega
  have hU : ¬ (a = 2 ∧ p = 3) → ¬ p ∣ Nat.card Kˣ := by
    rw [s16k_card_units_of_card hK]
    intro hne hdvd
    rcases ha with h1 | h2
    · rw [h1] at hdvd
      rw [show (2 : ℕ) ^ 1 - 1 = 1 by norm_num] at hdvd
      exact hp.not_dvd_one hdvd
    · rw [h2] at hdvd
      have hp3 : p = 3 :=
        (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1
          (by rwa [show (2 : ℕ) ^ 2 - 1 = 3 by norm_num] at hdvd)
      exact hne ⟨h2, hp3⟩
  by_cases hsp : a = 2 ∧ p = 3
  · obtain ⟨rfl, rfl⟩ := hsp
    have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
    have h3K : 3 ∣ Nat.card K - 1 := by norm_num [hK4]
    have h3K2 : 3 ∣ Nat.card K ^ 2 - 1 := by norm_num [hK4]
    by_cases hn4 : 4 ≤ n
    · exact h.false_of_fixNc hR hpσ (s16g_fixNc_statedSL_torus hn4 hp h3K)
    have hrk := s16k_pRank_le_statedSL (by omega) hp hp2 h3K hA ρ hρ hρN
    have hn3 : n = 3 := by omega
    subst hn3
    obtain ⟨hz, hmult⟩ := s16k_mult_sl3_four hGA hSL
    exact h.false_of_fixOrd hR hpσ (by rw [hz]; norm_num)
      (fun hd => absurd (hd.trans hmult) (by norm_num)) hrk
      (s16g_fixOrd_statedSL (by norm_num) hp h3K2)
  · have hpK : ¬ p ∣ Nat.card K := by
      rw [hK]
      intro hdvd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd))
    exact h.false_of_fixNc hR hpσ
      (s16k_fixNc_statedSL_of_pRank (by omega) hp hpK hA (hU hsp) ρ hρ hρN hrk3)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
