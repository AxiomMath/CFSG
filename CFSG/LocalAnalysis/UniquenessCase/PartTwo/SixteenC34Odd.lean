module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC34Aut
public import CFSG.Quasithin.Background.Asc81cTenFourA
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16c34_rk_wTil_eq_gamma_of_odd (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hodd : Odd (Nat.card ↥(barSub V₀ V h.isElemAbelian L))) :
    rk ↥(wTil V₀ V h.isElemAbelian L) = gamma15 D.M V₀ V h.isElemAbelian L := by
  have hV := h.isElemAbelian
  set V₁ : Subgroup G := v1Sub D.M V₀ V hV L with hV₁
  set W : Subgroup G := wSub V₀ V hV L with hW
  set Wt : Subgroup (Vtil V₀ V hV) := wTil V₀ V hV L with hWt
  set U : Subgroup (Vtil V₀ V hV) := imgTil V₀ V hV (V₁ ⊓ W) with hU
  have hUW : U ≤ Wt := by
    have h0 := Subgroup.map_mono (f := (mkTil V₀ V hV))
      (Subgroup.subgroupOf_mono V (inf_le_right : V₁ ⊓ W ≤ W))
    change imgTil V₀ V hV (V₁ ⊓ W) ≤ imgTil V₀ V hV W at h0
    rw [hW, wSub, imgTil_preTil] at h0
    exact h0
  have hfixU : U ≤ fixV (barSub V₀ V hV L) := by
    have h1 : imgTil V₀ V hV V₁ ≤ fixV (barSub V₀ V hV L) := by
      simpa only [conjSubgroup_one] using
        s15_Core_imgTil_v1Sub_le_fixV h (m := (1 : G)) D.M.one_mem
    have h0 := Subgroup.map_mono (f := (mkTil V₀ V hV))
      (Subgroup.subgroupOf_mono V (inf_le_left : V₁ ⊓ W ≤ V₁))
    change imgTil V₀ V hV (V₁ ⊓ W) ≤ imgTil V₀ V hV V₁ at h0
    exact h0.trans h1
  have hbot : fixV (barSub V₀ V hV L) ⊓ commSub ⊤ (barSub V₀ V hV L) = ⊥ :=
    CFSG.Quasithin.Asc81c.fixV_inf_commSub_eq_bot' (s15_Infra_vtil_sq_eq_one V₀ V hV) hodd
  have hU0 : U = ⊥ := by
    rw [eq_bot_iff, ← hbot]
    exact le_inf hfixU hUW
  have hrkU : rk ↥U = 0 := by
    rw [hU0]
    exact rk_bot
  have hW0 : V₀ ≤ W := by
    intro v hv0
    rw [hW, wSub, mem_preTil_iff_of_mem V₀ V hV _ (h.hyp125.pairFacts.le hv0)]
    have hvmod : IntMod.mk hV ⟨v, h.hyp125.pairFacts.le hv0⟩ ∈ modNull V₀ V hV := by
      rw [mem_modNull]
      exact hv0
    rw [show mkTil V₀ V hV (IntMod.mk hV ⟨v, h.hyp125.pairFacts.le hv0⟩) = 1 from
      (QuotientGroup.eq_one_iff (N := modNull V₀ V hV) _).2 hvmod]
    exact Wt.one_mem
  have h1 : mSub W = rk ↥Wt + mSub (W ⊓ V₀) := by
    have h1' := s15_Infra_mSub_eq_rk_imgTil_add V₀ V W hV (preTil_le V₀ V hV _)
    rwa [show imgTil V₀ V hV W = Wt from by rw [hW, wSub, imgTil_preTil]] at h1'
  have h2 : mSub (V₁ ⊓ W) = rk ↥U + mSub ((V₁ ⊓ W) ⊓ V₀) :=
    s15_Infra_mSub_eq_rk_imgTil_add V₀ V (V₁ ⊓ W) hV (inf_le_right.trans (preTil_le V₀ V hV _))
  have h3 : (V₁ ⊓ W) ⊓ V₀ = V₀ := by
    rw [inf_assoc, inf_eq_right.mpr hW0]
    exact inf_eq_right.mpr (s15_Infra_le_v1Sub D.M V₀ V hV L)
  have h4 : W ⊓ V₀ = V₀ := inf_eq_right.mpr hW0
  have h5 : mSub W = gamma15 D.M V₀ V hV L + delta15 D.M V₀ V hV L :=
    mSub_wSub (V₀ := V₀) (V := V) (L := L) D h.hyp125 hV
  rw [h3] at h2
  rw [h4] at h1
  change mSub W = gamma15 D.M V₀ V hV L + mSub (V₁ ⊓ W) at h5
  omega

theorem s16c34_card_lBar_dvd_168 (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hL : barSub V₀ V h.isElemAbelian L ≠ ⊥)
    (hγ : gamma15 D.M V₀ V h.isElemAbelian L ≤ 3) :
    Nat.card ↥(barSub V₀ V h.isElemAbelian L) ∣ 168 := by
  rw [Nat.card_congr (s15AWEquiv h1217 h hL).toEquiv]
  exact (Subgroup.card_subgroup_dvd_card (s15AW h)).trans
    (s16c34_card_mulAut_dvd_168 (s15_Three_wStar_exp h) hγ)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
