module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8RowBase
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Mult
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Small
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8TwoSL
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8TwoSp
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Bound
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Lift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem S16gRowCtx.false_of_binaryNaturalSL (h : S16gRowCtx D V₀ V L hV)
    (hGA : CFSG.Open.GriessAllModelsStatement) {n : ℕ} (hSL : IsSLn ↥(lBar V₀ V hV L) n 3)
    (hN : BinaryNaturalSL (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) n 3) : False := by
  obtain ⟨K, hF, hFin, hK, hR⟩ := hN
  letI := hF
  letI := hFin
  have hK8 : Nat.card K = 8 := by rw [hK]; norm_num
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
  by_cases hp3 : p = 3
  · subst hp3
    have hpK : 3 ∣ Nat.card K ^ 2 - 1 := by rw [hK8]; norm_num
    by_cases hn5 : 5 ≤ n
    · exact h.false_of_fixNc hR hpσ (s16g_fixNc_statedSL_blocks hn5 hp hpK)
    have hrk := s16g_pRank_le_statedSL_three (by omega) hK8 ρ hρ hρN
    by_cases hn4 : n = 4
    · subst hn4
      obtain ⟨hz, hmult⟩ := s16g_trivial_sl4 hGA hSL
      exact h.false_of_fixOrd hR hpσ (by rw [hz]; exact odd_one) (by rw [hmult]; norm_num)
        (by omega) (s16g_fixOrd_statedSL (by norm_num) hp hpK)
    · omega
  by_cases hp7 : p = 7
  · subst hp7
    have hpK : 7 ∣ Nat.card K ^ 2 - 1 := by rw [hK8]; norm_num
    by_cases hn4 : 4 ≤ n
    · exact h.false_of_fixNc hR hpσ
        (s16g_fixNc_statedSL_torus hn4 hp (by norm_num [hK8]))
    have hrk := s16g_pRank_le_statedSL_seven (by omega) hK8 ρ hρ hρN
    by_cases hn3 : n = 3
    · subst hn3
      obtain ⟨hz, hmult⟩ := s16g_trivial_sl3 hGA hSL
      exact h.false_of_fixOrd hR hpσ (by rw [hz]; exact odd_one) (by rw [hmult]; norm_num)
        (by omega) (s16g_fixOrd_statedSL (by norm_num) hp hpK)
    · omega
  exact h.false_of_fixNc hR hpσ
    (s16g_fixNc_statedSL_of_pRank (by omega) hK8 hp hp2 hp3 hp7 ρ hρ hρN hrk3)

theorem S16gRowCtx.false_of_natSp (h : S16gRowCtx D V₀ V L hV)
    (hGA : CFSG.Open.GriessAllModelsStatement) {n : ℕ} (hSp : IsSpn ↥(lBar V₀ V hV L) n 3)
    (hN : NatSpn (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) n 3) : False := by
  obtain ⟨hev, K, hF, hFin, hK, hR⟩ := hN
  letI := hF
  letI := hFin
  have hK8 : Nat.card K = 8 := by rw [hK]; norm_num
  generalize hm : n / 2 = m at hR
  by_cases hm0 : m = 0
  · subst hm0
    exact s16g_not_isQuasisimple_of_realizes_comm
      (fun x _ y _ => s16g_mul_comm_of_card_le_one (by simp) x y) hR h.quasi
  haveI : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, by omega⟩⟩
  obtain ⟨p, hpσ⟩ := h.std.hx.sig_nonempty
  have hp : p.Prime := (D.sig_prime p hpσ).1
  have hp2 : p ≠ 2 := (D.sig_prime p hpσ).2
  have hrk3 := h.three_le_pRank hpσ
  obtain ⟨ρ, hρ, hρN⟩ := h.exists_embedding hR
  by_cases hp37 : p = 3 ∨ p = 7
  · have hpK : p ∣ Nat.card K ^ 2 - 1 := by rw [hK8]; rcases hp37 with rfl | rfl <;> norm_num
    by_cases hm3 : 3 ≤ m
    · exact h.false_of_fixNc hR hpσ (s16g_fixNc_statedSp_blocks hm3 hp hpK)
    have hrk := s16g_pRank_le_statedSp (by omega) hK8 hp37 ρ hρ hρN
    by_cases hm2 : m = 2
    · subst hm2
      have hn4 : n = 4 := by obtain ⟨r, hr⟩ := hev; omega
      subst hn4
      obtain ⟨hz, hmult⟩ := s16g_trivial_sp4 hGA hSp
      exact h.false_of_fixOrd hR hpσ (by rw [hz]; exact odd_one)
        (by rw [hmult]; exact fun hd => hp.one_lt.ne' (Nat.dvd_one.1 hd)) (by omega)
        (s16g_fixOrd_statedSp (by norm_num) hp hpK)
    · omega
  · obtain ⟨hp3, hp7⟩ := not_or.1 hp37
    exact h.false_of_fixNc hR hpσ
      (s16g_fixNc_statedSp_of_pRank (by omega) hK8 hp hp2 hp3 hp7 ρ hρ hρN hrk3)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
