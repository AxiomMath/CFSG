module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35G7P1
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ChPlane

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.G7.P

open S35.Fin

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem comm_Wl_mem (hC : Ch.Ctx H M S) {γ : Geo H M} (hγ : vtype γ = false) {u : G}
    (hu1 : ∀ v ∈ Vn γ, ⁅u, v⁆ = 1) (hu2 : ∀ w ∈ Wb γ, ⁅w, u⁆ ∈ Vn γ)
    (hpl : ∀ μ ∈ nbrs γ, ∀ δ ∈ nbrs μ, δ ≠ γ → ∀ v ∈ Vn δ, ⁅v, u⁆ ∈ Vn γ ⊓ Vn δ)
    {l : Geo H M} (hl : l ∈ nbrs γ) {w : G} (hw : w ∈ Wl l) :
    ∃ h : w ∈ Wb γ, phiHom hC.sit γ u hu2 ⟨w, h⟩ ∈ (Ch.Rl γ l).subgroupOf (Vn γ) := by
  let T : Subgroup G := (((Ch.Rl γ l).subgroupOf (Vn γ)).comap (phiHom hC.sit γ u hu2)).map
    (Wb γ).subtype
  have hle : Wl l ≤ T := by
    refine Std.Wl_le fun ρ hρ v hv => ?_
    have hvW : v ∈ Wb γ := by
      by_cases hργ : ρ = γ
      · subst hργ; exact Std.Vn_le_Wb_self hC.sit hγ hv
      · exact Std.Vn_le_Wb (Std.dist_eq_two_iff.mpr ⟨l, hl, hρ, hργ⟩) hv
    refine Subgroup.mem_map.mpr ⟨⟨v, hvW⟩, Subgroup.mem_comap.mpr ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf, coe_phiHom]
    by_cases hργ : ρ = γ
    · subst hργ
      have : ⁅v, u⁆ = 1 := by
        rw [← commutatorElement_inv u v, hu1 v hv, inv_one]
      rw [this]; exact one_mem _
    · rw [hC.Rl_eq hγ hl hρ hργ]
      exact hpl l hl ρ hρ hργ v hv
  obtain ⟨x, hx, hxw⟩ := Subgroup.mem_map.mp (hle hw)
  have hxw' : (x : G) = w := hxw
  subst hxw'
  exact ⟨x.2, Subgroup.mem_comap.mp hx⟩

end S35.G7.P

end F53.Stellmacher

end CFSG.Quasithin
