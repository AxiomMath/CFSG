module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4SubLoc

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V} {T : Track Γ G}
  {a b : ℤ} {H : Subgroup G}

theorem IsPartner.smul (F : FanTree Γ G) {u w u' : V} (h : IsPartner Γ H u w u') {n : G}
    (hn : n ∈ H) : IsPartner Γ H (n • u) (n • w) (n • u') := by
  obtain ⟨hu', hne, hadj⟩ := h
  obtain ⟨k, hk, rfl⟩ := mem_orbit_subgroup.1 hu'
  refine ⟨mem_orbit_subgroup.2 ⟨n * k * n⁻¹, H.mul_mem (H.mul_mem hn hk) (H.inv_mem hn), ?_⟩,
    ?_, ?_⟩
  · rw [mul_smul, mul_smul, inv_smul_smul]
  · exact fun h => hne (MulAction.injective n h)
  · exact (F.adj_smul n _ _).2 hadj

namespace SubgraphProp

theorem orbit_nbr_subset (hS : SubgraphProp T a b H) (F : FanTree Γ G) {m : ℤ}
    (hm : b - a = 2 * m) {u' : V} (hu' : u' ∈ MulAction.orbit ↥H (T.line.vert a))
    (hadj : Γ.Adj u' (T.line.vert (a + 1))) : u' = T.line.vert a ∨ u' = T.line.vert (a + 2) := by
  obtain ⟨g, hg, rfl⟩ := mem_orbit_subgroup.1 hu'
  have hadj' : Γ.Adj (T.line.vert a) (g⁻¹ • T.line.vert (a + 1)) := by
    have := (F.adj_smul g⁻¹ _ _).2 hadj
    rwa [inv_smul_smul] at this
  obtain ⟨k, hk, hka, hkb⟩ := hS.loc_alpha F hm _ _ hadj' (T.line.adj a)
  have hkb' : k⁻¹ • T.line.vert (a + 1) = g⁻¹ • T.line.vert (a + 1) := by
    rw [inv_smul_eq_iff]
    exact hkb.symm
  have hka' : k⁻¹ • T.line.vert a = T.line.vert a := by
    rw [inv_smul_eq_iff]
    exact hka.symm
  have hsH : g * k⁻¹ ∈ H := H.mul_mem hg (H.inv_mem hk)
  have hs := hS.stab _ hsH (by rw [mul_smul, hkb', smul_inv_smul])
  rwa [mul_smul, hka'] at hs

theorem exists_map (hS : SubgraphProp T a b H) (F : FanTree Γ G) {m : ℤ} (hm : b - a = 2 * m)
    {u w : V} (hu : u ∈ MulAction.orbit ↥H (T.line.vert a)) (hw : Γ.Adj u w) :
    ∃ g ∈ H, g • T.line.vert a = u ∧ g • T.line.vert (a + 1) = w := by
  obtain ⟨h, hh, rfl⟩ := mem_orbit_subgroup.1 hu
  have hw' : Γ.Adj (T.line.vert a) (h⁻¹ • w) := by
    have := (F.adj_smul h⁻¹ _ _).2 hw
    rwa [inv_smul_smul] at this
  obtain ⟨k, hk, hka, hkb⟩ := hS.loc_alpha F hm _ _ (T.line.adj a) hw'
  refine ⟨h * k, H.mul_mem hh hk, ?_, ?_⟩
  · rw [mul_smul, hka]
  · rw [mul_smul, hkb, smul_inv_smul]

end SubgraphProp

theorem fan46_partner (hS : SubgraphProp T a b H) (F : FanTree Γ G) {m : ℤ} (hm : b - a = 2 * m)
    {u w : V} (hu : u ∈ MulAction.orbit ↥H (T.line.vert a)) (hw : Γ.Adj u w) :
    ∃ u', IsPartner Γ H u w u' ∧ ∀ u'', IsPartner Γ H u w u'' → u'' = u' := by
  obtain ⟨g, hgH, hgα, hgβ⟩ := hS.exists_map F hm hu hw
  have hτ : g * T.τ * g⁻¹ ∈ H := H.mul_mem (H.mul_mem hgH hS.tau) (H.inv_mem hgH)
  have hα₂ : T.line.vert a ≠ T.line.vert (a + 2) := T.line.nb a
  have hadj₂ : Γ.Adj (T.line.vert (a + 2)) (T.line.vert (a + 1)) := by
    have := (T.line.adj (a + 1)).symm
    rwa [show a + 1 + 1 = a + 2 by omega] at this
  refine ⟨g • T.line.vert (a + 2), ⟨mem_orbit_subgroup.2 ⟨g * T.τ * g⁻¹, hτ, ?_⟩, ?_, ?_⟩, ?_⟩
  · rw [← hgα, mul_smul, mul_smul, inv_smul_smul, T.trans]
  · rw [← hgα]
    exact fun h => hα₂ (MulAction.injective g h).symm
  · rw [← hgβ]
    exact (F.adj_smul g _ _).2 hadj₂
  · rintro u'' ⟨hu'', hne, hadj⟩
    obtain ⟨k, hk, rfl⟩ := mem_orbit_subgroup.1 hu''
    have horb : g⁻¹ • k • u ∈ MulAction.orbit ↥H (T.line.vert a) := by
      refine mem_orbit_subgroup.2 ⟨g⁻¹ * k * g, H.mul_mem (H.mul_mem (H.inv_mem hgH) hk) hgH, ?_⟩
      rw [← hgα]
      simp [mul_smul]
    have hgw : g⁻¹ • w = T.line.vert (a + 1) := by rw [← hgβ, inv_smul_smul]
    have hadj' : Γ.Adj (g⁻¹ • k • u) (T.line.vert (a + 1)) := by
      have := (F.adj_smul g⁻¹ _ _).2 hadj
      rwa [hgw] at this
    rcases hS.orbit_nbr_subset F hm horb hadj' with h | h
    · exfalso
      apply hne
      have := congrArg (g • ·) h
      simp only [smul_inv_smul] at this
      rw [this, hgα]
    · have := congrArg (g • ·) h
      simpa using this

end CFSG.Quasithin.Fan86
