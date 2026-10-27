module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightRowCtx

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem s16g_preBarSub_mono {M V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    {Xbar Ybar : Subgroup (MulAut (Vtil V₀ V hV))} (h : Xbar ≤ Ybar) :
    preBarSub M V₀ V hV Xbar ≤ preBarSub M V₀ V hV Ybar := by
  unfold preBarSub
  exact inf_le_inf_left _ (Subgroup.map_mono (Subgroup.comap_mono h))

private theorem s16g_layer_barImage {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hset : Setting16 D V₀ V L) {X : Subgroup G} (hXM : X ≤ D.M)
    (hbar : barSub V₀ V hV X = lBar V₀ V hV L)
    (hq : CFSG.Open.IsQuasisimple ↥(lBar V₀ V hV L))
    [((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal] :
    rankThreeLayer (F11.barImage11 D.M V₀ V X) = F11.barImage11 D.M V₀ V X := by
  have hMs : D.M ≤ stabTil V₀ V := s16g_le_stabTil hset
  set B : Subgroup (F11.MBar11 D.M V₀ V) := F11.barImage11 D.M V₀ V X with hBdef
  have hqB : CFSG.Open.IsQuasisimple ↥B := by
    obtain ⟨e, he⟩ := s15_Three_barImage_equiv (D := D) (V₀ := V₀) (V := V) hV hMs
    have hmap : B.map e.toMonoidHom = (lBar V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV) := by
      rw [hBdef, he X hXM, hbar]
    have hbarle : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV :=
      barSub_mono V₀ V hV hset.hyp151.le
    let eB : ↥B ≃* ↥(lBar V₀ V hV L) :=
      ((Subgroup.equivMapOfInjective B e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr hmap)).trans
        (Subgroup.subgroupOfEquivOfLe hbarle)
    exact CFSG.Open.IsQuasisimple.of_mulEquiv eB hq
  exact le_antisymm (sSup_le fun _ hK => hK.1)
    (le_sSup ⟨le_rfl, CFSG.Open.IsSubnormal.refl B, hqB⟩)

theorem s16g_exists_cover (D : Data G) (hS : S16gStd D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hset : Setting16 D V₀ V L)
    (hq : CFSG.Open.IsQuasisimple ↥(lBar V₀ V hV L)) :
    ∃ Y : Subgroup G, Y ≤ D.M ∧ ⁅Y, Y⁆ = Y ∧ F11.O2E Y = Y ∧
      Y ⊓ F11.CTilde D.M V₀ V ≤ OInf Y ∧ barSub V₀ V hV Y = lBar V₀ V hV L := by
  have hMs : D.M ≤ stabTil V₀ V := s16g_le_stabTil hset
  have hnormV : D.M ≤ normalizer (V : Set G) := hset.hyp16.hyp125.pairFacts.le_normalizer
  set X : Subgroup G := preBarSub D.M V₀ V hV (lBar V₀ V hV L) with hXdef
  have hX_le : X ≤ D.M := by rw [hXdef]; exact inf_le_left
  have hCX : F11.CTilde D.M V₀ V ≤ X := by
    rw [hXdef, cTilde_eq_preBarSub_bot hV hnormV]
    exact s16g_preBarSub_mono bot_le
  have hbarX : barSub V₀ V hV X = lBar V₀ V hV L := by
    rw [hXdef, barSub_preBarSub]
    exact inf_eq_left.2 (barSub_mono V₀ V hV hset.hyp151.le)
  let inst₀ : ((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal := s15_Three_cTilde_normal hV hMs
  haveI := inst₀
  have hlayerim : rankThreeLayer (F11.barImage11 D.M V₀ V X) = F11.barImage11 D.M V₀ V X :=
    s16g_layer_barImage hset hX_le hbarX hq
  obtain ⟨Y, hY, -⟩ :=
    hS.h119 V₀ V (Hyp125.hyp11 hS.h127 hset.hyp16.hyp125) X hCX hX_le hlayerim
  have hY_le : Y ≤ D.M := hY.1.trans hX_le
  have hYbar : F11.barImage11 D.M V₀ V Y = F11.barImage11 D.M V₀ V X := hY.2.2.2.2.2
  obtain ⟨e, he⟩ := s15_Three_barImage_equiv (D := D) (V₀ := V₀) (V := V) hV hMs
  have hbarY : barSub V₀ V hV Y = lBar V₀ V hV L := by
    have hsub : (barSub V₀ V hV Y).subgroupOf (Mbar D.M V₀ V hV) =
        (barSub V₀ V hV X).subgroupOf (Mbar D.M V₀ V hV) := by
      rw [← he Y hY_le, ← he X hX_le, hYbar]
    have h2 := congrArg (Subgroup.map (Subgroup.subtype (Mbar D.M V₀ V hV))) hsub
    simp only [Subgroup.subgroupOf_map_subtype] at h2
    rw [inf_eq_left.2 (barSub_mono V₀ V hV hY_le),
      inf_eq_left.2 (barSub_mono V₀ V hV hX_le), hbarX] at h2
    exact h2
  exact ⟨Y, hY_le, hY.2.1, hY.2.2.1, hY.2.2.2.2.1, hbarY⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
