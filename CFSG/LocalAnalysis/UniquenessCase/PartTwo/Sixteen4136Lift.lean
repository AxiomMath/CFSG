module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def liftO2 (M V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (Lbar : Subgroup (MulAut (Vtil V₀ V hV))) : Subgroup G :=
  twoResidual (preBarSub M V₀ V hV Lbar)

theorem liftO2_le (M V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (Lbar : Subgroup (MulAut (Vtil V₀ V hV))) : liftO2 M V₀ V hV Lbar ≤ M := by
  unfold liftO2 preBarSub
  exact (twoResidual_le _).trans inf_le_left

theorem twoResidual_liftO2 (M V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (Lbar : Subgroup (MulAut (Vtil V₀ V hV))) :
    twoResidual (liftO2 M V₀ V hV Lbar) = liftO2 M V₀ V hV Lbar := by
  unfold liftO2
  exact twoResidual_twoResidual _

theorem barSub_liftO2 {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) (hMs : M ≤ stabTil V₀ V)
    {Lbar : Subgroup (MulAut (Vtil V₀ V hV))} (hL : Lbar ≤ Mbar M V₀ V hV)
    (h2 : twoResidual Lbar = Lbar) : barSub V₀ V hV (liftO2 M V₀ V hV Lbar) = Lbar := by
  let Y := preBarSub M V₀ V hV Lbar
  let S := stabTil V₀ V
  let J : Subgroup ↥S := Y.subgroupOf S
  have hYS : Y ≤ S := by
    change preBarSub M V₀ V hV Lbar ≤ S
    unfold preBarSub
    exact inf_le_left.trans hMs
  have hbarY : barSub V₀ V hV Y = Lbar := by
    change barSub V₀ V hV (preBarSub M V₀ V hV Lbar) = Lbar
    rw [barSub_preBarSub, inf_eq_left.2 hL]
  have hJmap : J.map S.subtype = Y := Subgroup.map_subgroupOf_eq_of_le hYS
  have hres : (twoResidual J).map S.subtype = twoResidual Y := by
    rw [E1.map_twoResidual S.subtype J, hJmap]
  have hsub : (twoResidual Y).subgroupOf S = twoResidual J := by
    have h := Subgroup.comap_map_eq_self_of_injective (f := S.subtype) S.subtype_injective
      (twoResidual J)
    rw [hres] at h
    exact h
  have hcomm : barSub V₀ V hV (twoResidual Y) = twoResidual (barSub V₀ V hV Y) := by
    unfold barSub
    change ((twoResidual Y).subgroupOf S).map (actTil V₀ V hV) =
      twoResidual ((Y.subgroupOf S).map (actTil V₀ V hV))
    rw [hsub, E1.map_twoResidual (actTil V₀ V hV) J]
  rw [liftO2]
  change barSub V₀ V hV (twoResidual Y) = Lbar
  rw [hcomm, hbarY, h2]

theorem hyp151_liftO2 (D : Data G) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    {Lbar : Subgroup (MulAut (Vtil V₀ V h.isElemAbelian))}
    (hL : Lbar ≤ Mbar D.M V₀ V h.isElemAbelian) (h2 : twoResidual Lbar = Lbar)
    (hF : Fstar Lbar = Lbar)
    (hc : ∀ φ ∈ Mbar D.M V₀ V h.isElemAbelian,
      φ ∉ normalizer (Lbar : Set (MulAut (Vtil V₀ V h.isElemAbelian))) →
        ⁅Lbar, Lbar.map (MulAut.conj φ).toMonoidHom⁆ = ⊥ ∧
          commSub (commSub ⊤ Lbar) (Lbar.map (MulAut.conj φ).toMonoidHom) = ⊥) :
    Hyp151 D V₀ V (liftO2 D.M V₀ V h.isElemAbelian Lbar) := by
  let L := liftO2 D.M V₀ V h.isElemAbelian Lbar
  change Hyp151 D V₀ V L
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀
  have hbar : barSub V₀ V h.isElemAbelian L = Lbar :=
    barSub_liftO2 h.isElemAbelian hMs hL h2
  refine ⟨h, ?_, ?_, ?_, ?_⟩
  · exact liftO2_le D.M V₀ V h.isElemAbelian Lbar
  · exact twoResidual_liftO2 D.M V₀ V h.isElemAbelian Lbar
  · rw [hbar]
    exact hF
  · intro g hg hg_nbar
    let gbar : MulAut (Vtil V₀ V h.isElemAbelian) :=
      actTil V₀ V h.isElemAbelian ⟨g, hMs hg⟩
    have hconj : barSub V₀ V h.isElemAbelian (conjSubgroup L g) =
        Lbar.map (MulAut.conj gbar⁻¹).toMonoidHom := by
      rw [s15_Infra_barSub_conjSubgroup V₀ V h.isElemAbelian (hMs hg) L, hbar]
    have hmem : gbar⁻¹ ∈ Mbar D.M V₀ V h.isElemAbelian :=
      inv_mem (actTil_mem_barSub V₀ V h.isElemAbelian hg (hMs hg))
    have hnot : gbar⁻¹ ∉ normalizer (Lbar : Set (MulAut (Vtil V₀ V h.isElemAbelian))) := by
      intro hinn
      have hmapL : Lbar.map (MulAut.conj gbar⁻¹).toMonoidHom = Lbar :=
        (Subgroup.mem_normalizer_iff_map_conj_eq).1 hinn
      have hbar_g : barSub V₀ V h.isElemAbelian (conjSubgroup L g) =
          barSub V₀ V h.isElemAbelian L := by
        rw [hconj, hmapL, hbar]
      exact hg_nbar ((s15_Infra_mem_nBar_iff h h.isElemAbelian hg).2 hbar_g)
    obtain ⟨h1, h2c⟩ := hc gbar⁻¹ hmem hnot
    refine ⟨?_, ?_⟩
    · rw [hbar, hconj]
      exact h1
    · rw [wTil, hbar, hconj]
      exact h2c

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
