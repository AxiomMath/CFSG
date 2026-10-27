module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35L16Cs
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Ch2UC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.L16

open S35.Std S35.Fin S35.At S35.Ch2
open S34 (Cb)

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem cI_inf_Cb_le_Zv' (hS : Sit H M S) {δ : Geo H M} (hδ : vtype δ = false) {q : G}
    (hq : q ∈ stab δ) : cI hS δ hq ⊓ Cb δ ≤ Zv δ := by
  have hle : cI hS δ hq ≤ ⁅Vn δ, stab δ⁆ := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := mem_cI.mp hx
    have h1 : ⁅a, q⁆ ∈ ⁅Vn δ, stab δ⁆ := Subgroup.commutator_mem_commutator ha hq
    have e : q * a * q⁻¹ * a⁻¹ = ⁅a, q⁆⁻¹ := by rw [commutatorElement_def]; group
    rw [e]
    exact Subgroup.inv_mem _ h1
  exact fun x hx => UC.of_sit hS hδ ⟨hle hx.1, hx.2⟩

theorem rkZvEq_of_sit (hS : Sit H M S) : S35.II.RkZvEq H M := by
  intro δ hδ q hq
  have hZC : Zv δ ≤ Cb δ := S34.Zv_le_Cb hS.glob hδ
  have h1 : cI hS δ hq ⊓ Cb δ = cI hS δ hq ⊓ Zv δ :=
    le_antisymm (fun x hx => ⟨hx.1, cI_inf_Cb_le_Zv' hS hδ hq hx⟩) (inf_le_inf_left _ hZC)
  have h2 := relIndex_cI_Zv hS hδ hq
  have h3 := relIndex_cI_Cb hS δ hq
  rw [← h2, ← h1, h3]
  rfl

end S35.L16

end F53.Stellmacher

end CFSG.Quasithin
