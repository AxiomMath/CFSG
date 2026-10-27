module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8RowBase
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKLift
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKOmegaTwo
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSmall
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSmallShapes

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem s16k_false_of_natOmegaPlus (h : S16gRowCtx D V₀ V L hV)
    (hGA : CFSG.Open.GriessAllModelsStatement) {n a : ℕ} (ha : a = 1 ∨ a = 2)
    (hn : n ≠ 4 ∨ a = 1) (hΩ : IsOmegaPlus ↥(lBar V₀ V hV L) n a)
    (hN : NatOmegaPlus (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) n a) : False := by
  obtain ⟨hev, K, hF, hFin, hK, hR⟩ := hN
  letI := hF
  letI := hFin
  have ha1 : 1 ≤ a := by rcases ha with rfl | rfl <;> norm_num
  have ha2 : a ≤ 2 := by rcases ha with rfl | rfl <;> norm_num
  haveI : CharP K 2 := s16k_charP_two_of_card (a := a) ha1 hK
  generalize hm : n / 2 = m at hR
  have hm3 : 3 ≤ m := by
    rcases ha with rfl | rfl
    · have h6 := s16k_six_le_of_isOmegaPlus h.quasi hΩ
      omega
    · have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
      by_cases hm1 : m ≤ 1
      · exact (s16g_not_isQuasisimple_of_realizes_comm
          (s16k_comm_statedOmegaPlus_of_le_one_four hK4 hm1) hR h.quasi).elim
      · by_contra hlt
        obtain ⟨r, hr⟩ := hev
        exact (Or.resolve_right hn (by norm_num)) (by omega)
  haveI : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, by omega⟩⟩
  obtain ⟨p, hpσ⟩ := h.std.hx.sig_nonempty
  have hp : p.Prime := (D.sig_prime p hpσ).1
  have hp2 : p ≠ 2 := (D.sig_prime p hpσ).2
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    omega
  have hA : ¬ p ∣ Nat.card (RingAut K) := by
    rw [s16k_card_ringAut_of_card hK]
    intro hd
    have hpa : p ≤ a := Nat.le_of_dvd (by omega) hd
    omega
  have hdiv : Nat.card Kˣ ∣ Nat.card K ^ 2 - 1 := by
    rw [s16k_card_units_of_card hK, hK]
    rcases ha with rfl | rfl <;> norm_num
  have hrk3 := h.three_le_pRank hpσ
  obtain ⟨ρ, hρ, hρN⟩ := h.exists_embedding hR
  by_cases hpq : p ∣ Nat.card K ^ 2 - 1
  · rcases ha with rfl | rfl
    · have hK2 : Nat.card K = 2 := by rw [hK]; norm_num
      have hp_eq : p = 3 := by
        have h3 : p ∣ 3 := by
          rw [hK2] at hpq
          norm_num at hpq
          exact hpq
        exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3
      subst p
      exact h.false_of_fixNc hR hpσ (s16k_fixNc_statedOmegaPlus_two_two hK2 hm3)
    · exact h.false_of_fixNc hR hpσ
        (s16g_fixNc_statedOmegaPlus_two (by rw [hK]; norm_num) hm3 hp hp2 hpq)
  · have hU : ¬ p ∣ Nat.card Kˣ := fun hd => hpq (hd.trans hdiv)
    exact h.false_of_fixNc hR hpσ
      (s16k_fixNc_statedOmegaPlus_of_pRank hm3 hp hp2 hpq hA hU ρ hρ hρN hrk3)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
