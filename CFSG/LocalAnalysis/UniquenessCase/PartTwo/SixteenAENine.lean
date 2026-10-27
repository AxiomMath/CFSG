module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAENatFix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Rank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16c
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2
public import CFSG.LocalAnalysis.UniquenessCase.UC22DataExt
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16ae_false_of_case168_9_of_r16_4 (D : Data G) (hx : DataExt D) (h164 : R16_4 D)
    (h4 : 3 < CFSG.Open.evenRank G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Counterex16 D V₀ V L hV) (h9 : Case168_9 D V₀ V hV L) : False := by
  obtain ⟨-, -, hs, hnat, -⟩ := h9
  obtain ⟨-, hγ | h2 | h3 | h4'⟩ := h164 V₀ V L hV hc.setting hc.conc (by omega)
  · have hN := s16c167_natSum3_of_sumOfNat hnat
    have hfix : wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L) = ⊥ :=
      s16ae_natSum3_inf_fixV_eq_bot hN
    have hq := c8_mQuot_wTil_le_gamma15 D hc.setting.hyp151 hV
    rw [hfix] at hq
    have hm : E3.mQuot (wTil V₀ V hV L) ⊥ = rk ↥(wTil V₀ V hV L) := by
      unfold E3.mQuot
      rw [Subgroup.relIndex_bot_left]
      rfl
    have h9rk := s16c167_rk_natSum3 hN
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
