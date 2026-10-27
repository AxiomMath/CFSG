module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.FFC2Core

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.FFC CFSG.Open Subgroup
  CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem c23a_cross_fix {D : Data G} {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L) {x : G}
    (hx : x ∈ D.M) (hn : x ∉ nBar D.M V₀ V h.isElemAbelian L) :
    wTil V₀ V h.isElemAbelian L ≤
        fixV (barSub V₀ V h.isElemAbelian (conjSubgroup L x)) ∧
      wTil V₀ V h.isElemAbelian (conjSubgroup L x) ≤ fixV (barSub V₀ V h.isElemAbelian L) := by
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  have hxs : x ∈ stabTil V₀ V := hMs hx
  have hxs' : x⁻¹ ∈ stabTil V₀ V := (stabTil V₀ V).inv_mem hxs
  constructor
  · exact commSub_eq_bot_iff.1 (h.commute x hx hn).2
  · have hn' : x⁻¹ ∉ nBar D.M V₀ V h.isElemAbelian L :=
      fun hmem => hn ((Subgroup.inv_mem_iff (nBar D.M V₀ V h.isElemAbelian L)).1 hmem)
    have hfix' : wTil V₀ V h.isElemAbelian L ≤
        fixV (barSub V₀ V h.isElemAbelian (conjSubgroup L x⁻¹)) :=
      commSub_eq_bot_iff.1 (h.commute x⁻¹ (D.M.inv_mem hx) hn').2
    rw [s15_Infra_wTil_conjSubgroup V₀ V L h.isElemAbelian hxs]
    intro w hw
    rw [Subgroup.mem_map] at hw
    obtain ⟨w', hw', hw_eq⟩ := hw
    rw [mem_fixV]
    intro φ hφ
    let a : MulAut (Vtil V₀ V h.isElemAbelian) := actTil V₀ V h.isElemAbelian ⟨x, hxs⟩
    have ha : actTil V₀ V h.isElemAbelian ⟨x⁻¹, hxs'⟩ = a⁻¹ := by
      rw [show (⟨x⁻¹, hxs'⟩ : stabTil V₀ V) = (⟨x, hxs⟩ : stabTil V₀ V)⁻¹ from rfl,
        map_inv]
    have hmem : a * φ * a⁻¹ ∈ barSub V₀ V h.isElemAbelian (conjSubgroup L x⁻¹) := by
      rw [s15_Infra_barSub_conjSubgroup V₀ V h.isElemAbelian hxs' L, ha, inv_inv]
      exact ⟨φ, hφ, rfl⟩
    have hfixw' : (a * φ * a⁻¹) w' = w' := (mem_fixV.mp (hfix' hw')) _ hmem
    have hmain : φ w = w := by
      rw [← hw_eq]
      change φ (a⁻¹ w') = a⁻¹ w'
      calc φ (a⁻¹ w') = a⁻¹ ((a * φ * a⁻¹) w') := by
            rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
        _ = a⁻¹ w' := by rw [hfixw']
    exact hmain

theorem c23a_z_ne_bot {D : Data G} {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L) (h0 : V₀ = ⊥)
    (hne : v1Sub D.M V₀ V h.isElemAbelian L ≠ ⊥) :
    wTil V₀ V h.isElemAbelian L ⊓ fixV (barSub V₀ V h.isElemAbelian L) ≠ ⊥ := by
  intro hbot
  have hsub : wSub V₀ V h.isElemAbelian L ⊓ centralizer (L : Set G) = ⊥ := by
    refine le_bot_iff.1 fun g hg => ?_
    have hgW : g ∈ wSub V₀ V h.isElemAbelian L := hg.1
    have hgV : g ∈ V := preTil_le V₀ V h.isElemAbelian (wTil V₀ V h.isElemAbelian L) hgW
    let x : IntMod V h.isElemAbelian := IntMod.mk h.isElemAbelian ⟨g, hgV⟩
    have hqW : mkTil V₀ V h.isElemAbelian x ∈ wTil V₀ V h.isElemAbelian L :=
      (mem_preTil_iff_of_mem V₀ V h.isElemAbelian (wTil V₀ V h.isElemAbelian L) hgV).1 hgW
    have hqfix : mkTil V₀ V h.isElemAbelian x ∈ fixV (barSub V₀ V h.isElemAbelian L) := by
      rw [mem_fixV]
      intro φ hφ
      obtain ⟨l, hlL, hlφ⟩ := (mem_barSub V₀ V h.isElemAbelian L φ).1 hφ
      have hst : actStab V₀ V h.isElemAbelian l x = x := by
        refine IntMod.val_injective ?_
        rw [actStab_apply_val]
        have hc : (l : G) * g = g * (l : G) :=
          (Subgroup.mem_centralizer_iff).1 hg.2 (l : G) hlL
        change (l : G) * g * (l : G)⁻¹ = g
        rw [hc]
        group
      rw [← hlφ, actTil_mk, hst]
    have hqbot : mkTil V₀ V h.isElemAbelian x ∈
        (⊥ : Subgroup (Vtil V₀ V h.isElemAbelian)) := by
      rw [← hbot]
      exact ⟨hqW, hqfix⟩
    have hqone : mkTil V₀ V h.isElemAbelian x = 1 := Subgroup.mem_bot.1 hqbot
    have hxmod : x ∈ modNull V₀ V h.isElemAbelian := by
      have hmemker : x ∈ (mkTil V₀ V h.isElemAbelian).ker := MonoidHom.mem_ker.2 hqone
      unfold mkTil at hmemker
      rwa [QuotientGroup.ker_mk'] at hmemker
    have hx0 : x.val ∈ V₀ := (mem_modNull V₀ V h.isElemAbelian x).1 hxmod
    have hx0' : x.val ∈ (⊥ : Subgroup G) := by simpa only [h0] using hx0
    have hg1 : g = 1 := Subgroup.mem_bot.1 hx0'
    exact Subgroup.mem_bot.2 hg1
  have hbot1 : v1Sub D.M V₀ V h.isElemAbelian L = ⊥ := by
    rw [v1Sub_of_eq_bot D.M V₀ V h.isElemAbelian L h0]
    simp only [hsub, E3.conjSubgroup_bot, iSup_const]
  exact hne hbot1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
