module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8RowBase
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Small
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8TwoSp
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKBound
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKMult

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem s16k_false_of_natSp (h : S16gRowCtx D V₀ V L hV)
    (hGA : CFSG.Open.GriessAllModelsStatement) {n a : ℕ} (ha : a = 1 ∨ a = 2)
    (hSp : IsSpn ↥(lBar V₀ V hV L) n a)
    (hN : NatSpn (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) n a) : False := by
  obtain ⟨hev, K, hF, hFin, hK, hR⟩ := hN
  letI := hF
  letI := hFin
  generalize hm : n / 2 = m at hR
  by_cases hm0 : m = 0
  · subst hm0
    exact s16g_not_isQuasisimple_of_realizes_comm
      (fun x _ y _ => s16g_mul_comm_of_card_le_one (by simp) x y) hR h.quasi
  haveI : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, by omega⟩⟩
  obtain ⟨p, hpσ⟩ := h.std.hx.sig_nonempty
  have hp : p.Prime := (D.sig_prime p hpσ).1
  have hp2 : p ≠ 2 := (D.sig_prime p hpσ).2
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hrk3 := h.three_le_pRank hpσ
  obtain ⟨ρ, hρ, hρN⟩ := h.exists_embedding hR
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
  have hA : ¬ p ∣ Nat.card (RingAut K) := by
    rw [s16k_card_ringAut_of_card hK]
    intro hd
    have hle : p ≤ a := Nat.le_of_dvd (by rcases ha with h | h <;> omega) hd
    rcases ha with h | h <;> omega
  have hU' : ¬ (a = 2 ∧ p = 3) → ¬ p ∣ Nat.card Kˣ := by
    intro hna hd
    rw [s16k_card_units_of_card hK] at hd
    rcases ha with h | h
    · rw [h] at hd
      exact hp.not_dvd_one (by simpa using hd)
    · rw [h] at hd
      exact hna ⟨h, (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (by simpa using hd)⟩
  by_cases hspecial : a = 2 ∧ p = 3
  · obtain ⟨rfl, rfl⟩ := hspecial
    have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
    have hpK15 : 3 ∣ Nat.card K ^ 2 - 1 := by rw [hK4]; norm_num
    have hU3 : Nat.card Kˣ = 3 := by rw [s16k_card_units_of_card hK]; norm_num
    by_cases hm3 : 3 ≤ m
    · exact h.false_of_fixNc hR hpσ (s16g_fixNc_statedSp_blocks hm3 hp hpK15)
    · have hrk : CFSG.Open.pRank 3 (Mbar D.M V₀ V hV) ≤ m + 1 :=
        s16k_pRank_le_statedSp (by omega) hp hp2 hpK15 hA hU3 ρ hρ hρN
      have hm2 : m = 2 := by omega
      subst hm2
      have hn4 : n = 4 := by obtain ⟨r, hr⟩ := hev; omega
      subst hn4
      obtain ⟨hz, hmult⟩ := s16k_trivial_sp4_four hGA hSp
      exact h.false_of_fixOrd hR hpσ (by rw [hz]; exact odd_one)
        (by rw [hmult]; exact fun hd => hp.one_lt.ne' (Nat.dvd_one.1 hd)) (by omega)
        (s16g_fixOrd_statedSp (by norm_num) hp hpK15)
  · exact h.false_of_fixNc hR hpσ
      (s16k_fixNc_statedSp_of_pRank (by omega) hp hpK hA (hU' hspecial) ρ hρ hρN hrk3)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
