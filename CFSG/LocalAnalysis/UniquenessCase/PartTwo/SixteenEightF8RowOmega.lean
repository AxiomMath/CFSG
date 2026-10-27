module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8RowBase
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatScalars
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Mult
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Small
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8TwoOmega
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Bound
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Lift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.RankThree.GF2n.Stroth80

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem S16gRowCtx.range_le_lin (h : S16gRowCtx D V₀ V L hV) (hpσ : 3 ∈ D.sig) {ι : Type}
    [Fintype ι] [DecidableEq ι] [Nonempty ι] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 8) {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)}
    (hΓ : AddCommutantScalar Γ)
    {ρ : ↥(Mbar D.M V₀ V hV) →* MulAut (Multiplicative (ι → K))}
    (hρN : ∀ a : ↥(Mbar D.M V₀ V hV), ρ a ∈ s16gNorm Γ) : ρ.range ≤ s16gLin ι K := by
  refine s16g_le_lin_of_hom_trivial hΓ (s16g_range_le_norm hρN) fun φ => ?_
  have hC : ∀ c : RingAut K, c ^ 3 = 1 := fun c => by
    have h3 := pow_card_eq_one' (G := RingAut K) (x := c)
    rwa [s16g_card_ringAut_eight hK] at h3
  have h1 := h.hom_eq_one hpσ hC (φ.comp ρ.rangeRestrict)
  refine MonoidHom.ext fun x => ?_
  obtain ⟨a, rfl⟩ := ρ.rangeRestrict_surjective x
  exact DFunLike.congr_fun h1 a

theorem S16gRowCtx.false_of_natOmegaPlus (h : S16gRowCtx D V₀ V L hV) {n : ℕ} (hn : n ≠ 4)
    (hN : NatOmegaPlus (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) n 3) : False := by
  obtain ⟨hev, K, hF, hFin, hK, hR⟩ := hN
  letI := hF
  letI := hFin
  have hK8 : Nat.card K = 8 := by rw [hK]; norm_num
  haveI := s16g_charP_two hK8
  generalize hm : n / 2 = m at hR
  by_cases hm1 : m ≤ 1
  · exact s16g_not_isQuasisimple_of_realizes_comm
      (s16g_comm_statedOmegaPlus_of_le_one hK8 hm1) hR h.quasi
  have hm3 : 3 ≤ m := by
    by_contra hlt
    obtain ⟨r, hr⟩ := hev
    exact hn (by omega)
  haveI : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, by omega⟩⟩
  obtain ⟨p, hpσ⟩ := h.std.hx.sig_nonempty
  have hp : p.Prime := (D.sig_prime p hpσ).1
  have hp2 : p ≠ 2 := (D.sig_prime p hpσ).2
  have hrk3 := h.three_le_pRank hpσ
  obtain ⟨ρ, hρ, hρN⟩ := h.exists_embedding hR
  by_cases hp37 : p = 3 ∨ p = 7
  · have hpK : p ∣ Nat.card K ^ 2 - 1 := by rw [hK8]; rcases hp37 with rfl | rfl <;> norm_num
    exact h.false_of_fixNc hR hpσ
      (s16g_fixNc_statedOmegaPlus_two (by rw [hK8]; norm_num) hm3 hp hp2 hpK)
  · obtain ⟨hp3, hp7⟩ := not_or.1 hp37
    exact h.false_of_fixNc hR hpσ
      (s16g_fixNc_statedOmegaPlus_of_pRank hm3 hK8 hp hp2 hp3 hp7 ρ hρ hρN hrk3)

theorem S16gRowCtx.false_of_natOmegaMinus (h : S16gRowCtx D V₀ V L hV)
    (hGA : CFSG.Open.GriessAllModelsStatement) {n : ℕ}
    (hΩ : IsOmegaMinus ↥(lBar V₀ V hV L) n 3)
    (hN : NatOmegaMinus (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) n 3) : False := by
  obtain ⟨hev, K, hF, hFin, b, c, hK, hirr, hR⟩ := hN
  letI := hF
  letI := hFin
  have hK8 : Nat.card K = 8 := by rw [hK]; norm_num
  haveI := s16g_charP_two hK8
  generalize hm : n / 2 = m at hR
  by_cases hm1 : m ≤ 1
  · exact s16g_not_isQuasisimple_of_realizes_comm
      (s16g_comm_statedOmegaMinus_of_le_one hK8 hirr hm1) hR h.quasi
  haveI : Nonempty (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
  obtain ⟨p, hpσ⟩ := h.std.hx.sig_nonempty
  have hp : p.Prime := (D.sig_prime p hpσ).1
  have hp2 : p ≠ 2 := (D.sig_prime p hpσ).2
  have hrk3 := h.three_le_pRank hpσ
  obtain ⟨ρ, hρ, hρN⟩ := h.exists_embedding hR
  by_cases hp37 : p = 3 ∨ p = 7
  · have hpK : p ∣ Nat.card K ^ 2 - 1 := by rw [hK8]; rcases hp37 with rfl | rfl <;> norm_num
    by_cases hm4 : 4 ≤ m
    · exact h.false_of_fixNc hR hpσ
        (s16g_fixNc_statedOmegaMinus_two (by rw [hK8]; norm_num) hm4 hirr hp hp2 hpK)
    by_cases hm3 : m = 3
    · have hrk : CFSG.Open.pRank p (Mbar D.M V₀ V hV) ≤ 3 := by
        rcases hp37 with rfl | rfl
        · have hΓ := addCommutantScalar_statedOmegaMinus (m := m) (b := b) (c := c)
            (by omega) hirr
          exact s16g_pRank_le_statedOmegaMinus_three_three hK8 hirr hm3 ρ hρ hρN
            (h.range_le_lin hpσ hK8 hΓ hρN)
        · exact s16g_pRank_le_statedOmegaMinus_three_seven hK8 hirr hm3 ρ hρ hρN
      subst hm3
      have hn6 : n = 6 := by obtain ⟨r, hr⟩ := hev; omega
      subst hn6
      obtain ⟨hz, hmult⟩ := s16g_trivial_omegaMinus6 hGA hΩ
      exact h.false_of_fixOrd hR hpσ (by rw [hz]; exact odd_one)
        (by rw [hmult]; exact fun hd => hp.one_lt.ne' (Nat.dvd_one.1 hd)) hrk
        (s16g_fixOrd_statedOmegaMinus_three (by rw [hK8]; norm_num) hirr hp hp2 hpK)
    · have hm2 : m = 2 := by omega
      have hrk := s16g_pRank_le_statedOmegaMinus_two hK8 hirr hm2 hp37 ρ hρ hρN
      omega
  · obtain ⟨hp3, hp7⟩ := not_or.1 hp37
    by_cases hm3 : 3 ≤ m
    · exact h.false_of_fixNc hR hpσ
        (s16g_fixNc_statedOmegaMinus_of_pRank hm3 hK8 hirr hp hp2 hp3 hp7 ρ hρ hρN hrk3)
    · have hm2 : m = 2 := by omega
      have hrk := s16g_pRank_le_statedOmegaMinus_two_generic hK8 hirr hm2 hp hp2 hp3 hp7 ρ hρ hρN
      omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
