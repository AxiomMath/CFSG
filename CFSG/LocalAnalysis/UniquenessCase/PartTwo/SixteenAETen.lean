module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Norm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Rank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16c
public import CFSG.Quasithin.Background.Asc81cTenFourA
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16ae_false_of_case168_10_of_r16_4 (D : Data G) (hx : DataExt D) (h164 : R16_4 D)
    (h4 : 3 < CFSG.Open.evenRank G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Counterex16 D V₀ V L hV) (h10 : Case168_10 D V₀ V hV L) : False := by
  obtain ⟨p, hp, hcyc, hrk, hs, hsig, -⟩ := h10
  have hpσ : p ∈ D.sig := by
    rw [hsig]
    exact Set.mem_singleton p
  have hF4 : 4 ≤ CFSG.Open.pRank p D.M := hx.four_le h4 p hpσ
  obtain ⟨-, hγ | h2 | h3 | h4'⟩ := h164 V₀ V L hV hc.setting hc.conc (by omega)
  · have hodd : Odd (Nat.card ↥(lBar V₀ V hV L)) := by
      rw [hcyc.2]
      rcases hp with rfl | rfl <;> decide
    have hfix : wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L) = ⊥ :=
      (inf_comm _ _).trans
        (Asc81c.fixV_inf_commSub_eq_bot' (s15_Infra_vtil_sq_eq_one V₀ V hV) hodd)
    have hq := c8_mQuot_wTil_le_gamma15 D hc.setting.hyp151 hV
    rw [hfix] at hq
    have hm : E3.mQuot (wTil V₀ V hV L) ⊥ = rk ↥(wTil V₀ V hV L) := by
      unfold E3.mQuot
      rw [Subgroup.relIndex_bot_left]
      rfl
    have hd : 2 ≤ dParam p := by
      rcases hp with rfl | rfl
      · rw [s16c1610_dParam_three]
      · rw [s16c1610_dParam_seven]
        norm_num
    omega
  · have h3σ : 3 ∈ D.sig := by
      rw [h2.2.1]
      exact Set.mem_singleton 3
    have := hx.four_le h4 3 h3σ
    have h33 := h2.2.2.1
    omega
  · have h7σ : 7 ∈ D.sig := by
      rw [h3.2.2.1]
      exact Set.mem_singleton 7
    have := hx.four_le h4 7 h7σ
    have h73 := h3.2.2.2.1
    omega
  · obtain ⟨q, -, -, -, hq, hF3, -⟩ := h4'
    have hqσ : q ∈ D.sig := by
      rw [hq]
      exact Set.mem_singleton q
    have := hx.four_le h4 q hqσ
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
