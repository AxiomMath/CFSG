module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35T2LB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.T2L

open S35.Std

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem link_of_K0 (hS : Sit H M S) (I : Inputs H M) {β l : Geo H M} (hβ : vtype β = false)
    (hl : l ∈ nbrs β) {x : G} (hx : x ∈ stab β) (hmov : x ∉ Subgroup.normalizer (Zv l : Set G))
    {K₀ : Subgroup G} (hKi : K₀.relIndex (Wb β) ≤ 2) (hKx : ∀ h ∈ K₀, ⁅h, x⁆ ∈ Vn β) :
    (Wl l ⊓ conjSub x⁻¹ (Wl l)).relIndex (Wl l) = 2 ∧ Wl l ⊓ conjSub x⁻¹ (Wl l) ≤ K₀ := by
  have hβl : β ∈ nbrs l := mem_nbrs_symm.mpr hl
  have hA : Wl l ⊓ K₀ ≤ Wl l ⊓ conjSub x⁻¹ (Wl l) := by
    rintro w ⟨hwW, hwK⟩
    refine ⟨hwW, ?_⟩
    show w ∈ conjSub x⁻¹ (Wl l)
    rw [mem_conjSub, inv_inv]
    have hc : ⁅w⁻¹, x⁆ ∈ Vn β := hKx _ (K₀.inv_mem hwK)
    have e : x * w * x⁻¹ = w * ⁅w⁻¹, x⁆ := by rw [commutatorElement_def]; group
    rw [e]
    exact (Wl l).mul_mem hwW (Vn_le_Wl hβl hc)
  have hmov' : x⁻¹ ∉ Subgroup.normalizer (Zv l : Set G) := fun h =>
    hmov ((Subgroup.inv_mem_iff _).mp h)
  have hne : Wl l ⊓ conjSub x⁻¹ (Wl l) ≠ Wl l := fun h =>
    not_le_conj hS I hβ hl ((stab β).inv_mem hx) hmov' (inf_eq_left.mp h)
  have hrel : (Wl l ⊓ K₀).relIndex (Wl l) ≤ 2 := by
    rw [Subgroup.inf_relIndex_left]
    exact (Subgroup.relIndex_le_of_le_right (Wl_le_Wb hS hβ hl) (relIndex_ne_zero' K₀ _)).trans hKi
  obtain ⟨hAB, hBi⟩ := eq_of_relIndex_le_two hrel hA inf_le_left hne
  exact ⟨hBi, by rw [← hAB]; exact inf_le_right⟩

theorem step2L_of_inputs (hS : Sit H M S) (I : Inputs H M) (hZI : S35.II.ZvInf H M) :
    S35.II.Step2L H M := by
  intro hN β hβ x hx hxQ _ K₀ hVK hKW hKi hKx
  have hex : ∃ l ∈ nbrs β, x ∉ Subgroup.normalizer (Zv l : Set G) := by
    by_contra hcon
    exact hxQ (hZI β hβ x hx fun l hl => by
      by_contra hn
      exact hcon ⟨l, hl, hn⟩)
  obtain ⟨l, hl, hmov⟩ := hex
  obtain ⟨hlink, hle⟩ := link_of_K0 hS I hβ hl hx hmov hKi hKx
  have hmov' : x⁻¹ ∉ Subgroup.normalizer (Zv l : Set G) := fun h =>
    hmov ((Subgroup.inv_mem_iff _).mp h)
  exact ⟨_, commonHyp_of_link_aux hS hN I hβ hl ((stab β).inv_mem hx) hmov' hlink, hle⟩

end S35.T2L

end F53.Stellmacher

end CFSG.Quasithin
