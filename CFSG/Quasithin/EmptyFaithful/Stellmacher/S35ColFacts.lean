module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ColZ

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.Col

open S35.Std S35.Fin S35.Ch S35.Ch2
open S34 (Cb)

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem Uc_eq_comm_stab (hS : Sit H M S) {δ : Geo H M} (hδ : vtype δ = false) :
    Uc δ = ⁅Vn δ, stab δ⁆ := by
  apply le_antisymm
  · refine sup_le (Subgroup.commutator_mono le_rfl (oTwoRes_le _)) ?_
    rw [← comm_Vn_Qv hS hδ]
    exact Subgroup.commutator_mono le_rfl (pCoreOf_le 2 _)
  · rw [Subgroup.commutator_le]
    intro u hu f hf
    have e : ⁅u, f⁆ = (f * u * f⁻¹ * u⁻¹)⁻¹ := by rw [commutatorElement_def]; group
    rw [e]
    exact (Uc δ).inv_mem (comm_Vn_le_Uc hS hδ hf hu)

theorem mem_Uc_iff_of_mem_Zv_nbr (hS : Sit H M S) {δ l : Geo H M} (hδ : vtype δ = false)
    (hl : l ∈ nbrs δ) {z : G} (hz : z ∈ Zv l) (hzZ : z ∉ Zv δ) :
    z ∈ Uc δ ↔ Cb δ = Zv δ := by
  constructor
  · intro h
    by_contra hne
    exact hzZ (Zv_nbr_inf_Uc hS hδ hl hne ▸ (⟨hz, h⟩ : z ∈ Zv l ⊓ Uc δ))
  · intro h
    exact (Zv_nbr_le_Uc_iff_Cb hS hδ hl).mpr h hz

theorem π_eq_vp_of_mem_Zv_nbr {δ : Geo H M} (c : Chart2 δ) (hS : Sit H M S)
    (hδ : vtype δ = false) {l : Geo H M} (hl : l ∈ nbrs δ) {z : G} (hz : z ∈ Zv l)
    (hzZ : z ∉ Zv δ) : c.π ⟨z, Std.Zv_le_Vn hl hz⟩ = vp (c.pt l) :=
  π_eq_vp c hS hδ hl hz fun h => hzZ (by
    have : z ∈ Cb δ ⊓ Zv l := ⟨h, hz⟩
    rwa [S34.Cb_inf_Zv_eq hS.glob hδ hl] at this)

theorem Mbl_maximal (hS : Sit H M S) {δ l : Geo H M} (hδ : vtype δ = false) (hl : l ∈ nbrs δ) :
    Mbl δ l ≠ stab δ ∧ stab δ ⊓ stab l ≤ Mbl δ l ∧
      ∀ P : Subgroup G, P ≤ stab δ → stab δ ⊓ stab l ≤ P → P = stab δ ∨ P ≤ Mbl δ l := by
  obtain ⟨c⟩ := exists_chart2 hS hδ
  refine ⟨c.Mbl_ne_stab hS hδ hl, inf_le_Mbl hS, fun P hP hinf => ?_⟩
  rw [Mbl_eq_preθ c hS hδ hl]
  exact c.eq_or_le_preθ_pt hS hδ hl hP hinf

end S35.Col

end F53.Stellmacher

end CFSG.Quasithin
