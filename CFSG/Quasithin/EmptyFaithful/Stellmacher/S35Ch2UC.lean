module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ColGrp2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Ch2That

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.Ch2

open S35.Std S35.Fin S35.Ch S35.II
open S34 (Cb)

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem UC.of_sit (hS : Sit H M S) {δ : Geo H M} (hδ : vtype δ = false) : UC δ := by
  have h : ⁅Vn δ, stab δ⁆ ≤ S35.Col.Uc δ := by
    rw [Subgroup.commutator_le]
    intro u hu f hf
    have e : ⁅u, f⁆ = (f * u * f⁻¹ * u⁻¹)⁻¹ := by rw [commutatorElement_def]; group
    rw [e]
    exact (S35.Col.Uc δ).inv_mem (S35.Col.comm_Vn_le_Uc hS hδ hf hu)
  intro x hx
  have := S35.Col.Uc_inf_Cb hS hδ
  exact this.le ⟨h hx.1, hx.2⟩

namespace Chart2

variable {δ : Geo H M} (c : Chart2 δ)

include c

theorem bar_That2' (hS : Sit H M S) (hδ : vtype δ = false) {l : Geo H M} (hl : l ∈ nbrs δ) :
    c.bar (That2 δ l) = That (c.Dl l) :=
  c.bar_That2 hS hδ (UC.of_sit hS hδ) hl

theorem relIndex_That2' (hS : Sit H M S) (hδ : vtype δ = false) {l : Geo H M}
    (hl : l ∈ nbrs δ) : (That2 δ l).relIndex (stab δ ⊓ stab l) = 2 :=
  c.relIndex_That2 hS hδ (UC.of_sit hS hδ) hl

theorem relIndex_Zv_Plane2' (hS : Sit H M S) (hδ : vtype δ = false) {l : Geo H M}
    (hl : l ∈ nbrs δ) : (Zv δ).relIndex (Plane2 δ l) = 4 :=
  c.relIndex_Zv_Plane2 hS hδ (UC.of_sit hS hδ) hl

theorem commutator_le_Plane2' (hS : Sit H M S) (hδ : vtype δ = false) {l : Geo H M}
    (hl : l ∈ nbrs δ) {K : Subgroup G} (hK : K ≤ That2 δ l) : ⁅Vn δ, K⁆ ≤ Plane2 δ l :=
  c.commutator_le_Plane2 hS hδ (UC.of_sit hS hδ) hl hK

end Chart2

theorem thatFacts (hS : Sit H M S) : ThatFacts H M := fun δ l hδ hl => by
  obtain ⟨c⟩ := exists_chart2 hS hδ
  exact ⟨Qv_le_That2 hS hδ hl, That2_le_inf hS δ l, c.relIndex_That2' hS hδ hl⟩

end S35.Ch2

end F53.Stellmacher

end CFSG.Quasithin
