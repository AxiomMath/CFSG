module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Ch2Syl
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ChZl

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.Ch2

open S35.Std S35.Fin S35.Ch
open S34 (Cb)

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem not_Zv_nbr_le_Cb (hS : Sit H M S) {δ l : Geo H M} (hδ : vtype δ = false)
    (hl : l ∈ nbrs δ) : ¬ Zv l ≤ Cb δ := by
  intro h
  have h1 := S34.Cb_inf_Zv_eq hS.glob hδ hl
  rw [inf_eq_right.mpr h] at h1
  have h2 := hS.cardZ3 l (vtype_nbr_S5 hδ hl)
  rw [h1, hS.cardZ5 δ hδ] at h2
  omega

namespace Chart2

variable {δ : Geo H M} (c : Chart2 δ)

include c

theorem Zv_nbr_le_fixSecIn (hS : Sit H M S) (hδ : vtype δ = false) {l : Geo H M}
    (hl : l ∈ nbrs δ) : Zv l ≤ fixSecIn (stab δ ⊓ stab l) (Cb δ) (Vn δ) := by
  intro z hz
  have hzV : z ∈ Vn δ := Zv_le_Vn hl hz
  refine (c.mem_fixSecIn_iff inf_le_left ⟨z, hzV⟩).mpr ?_
  rw [mem_fixW]
  intro σ hσ
  obtain ⟨a, ha, rfl⟩ := (c.mem_bar_iff).mp hσ
  exact (c.comm_mem_iff a ⟨z, hzV⟩).mp
    (S34.Zv_le_Cb hS.glob hδ (comm_mem_Zv_nbr hS hδ hl ha hz))

theorem img_Zv_nbr_le (hS : Sit H M S) (hδ : vtype δ = false) {l : Geo H M} (hl : l ∈ nbrs δ) :
    c.img (Zv l) ≤ Subgroup.zpowers (vp (fixPt (c.Dl l))) := by
  have h1 := c.img_mono (c.Zv_nbr_le_fixSecIn hS hδ hl)
  rw [c.img_fixSecIn inf_le_left] at h1
  have h2 : c.bar (stab δ ⊓ stab l) = c.Dl l := rfl
  rw [h2] at h1
  exact (fixW_sylow (c.card_Dl hS hl) (isFixPt_fixPt (c.card_Dl hS hl))) ▸ h1

theorem img_Zv_nbr (hS : Sit H M S) (hδ : vtype δ = false) {l : Geo H M} (hl : l ∈ nbrs δ) :
    c.img (Zv l) = Subgroup.zpowers (vp (fixPt (c.Dl l))) := by
  refine le_antisymm (c.img_Zv_nbr_le hS hδ hl) ?_
  have hne : c.img (Zv l) ≠ ⊥ := fun h =>
    not_Zv_nbr_le_Cb hS hδ hl ((c.img_eq_bot_iff (Zv_le_Vn hl)).mp h)
  obtain ⟨w, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hle := c.img_Zv_nbr_le hS hδ hl w.2
  rcases (mem_zpowers_iff_of_mul_self (vp_mul_self (fixPt (c.Dl l)))).mp hle with h | h
  · exact absurd (Subtype.ext h) hw1
  · rw [Subgroup.zpowers_le, ← h]
    exact w.2

end Chart2

end S35.Ch2

end F53.Stellmacher

end CFSG.Quasithin
