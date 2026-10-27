module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ChPlane
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.Ch

open S35.Std S35.Fin

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem vp_ne_ep (p : Fin 5) {a b : Fin 5} (hab : a ≠ b) : vp p ≠ ep a b := by
  intro h
  have := wtO_vp p
  rw [h, wtO_ep hab] at this
  omega

namespace Chart

variable {δ : Geo H M} (c : Chart δ)

include c

theorem img_Rl (hC : Ctx H M S) (hδ : vtype δ = false) {l : Geo H M} (hl : l ∈ nbrs δ) :
    c.img (Rl δ l) = commW orth (Subgroup.zpowers (zc (c.Dl l))) ⊤ :=
  eq_commW_z_of_card_four (c.card_Dl hC.sit hl) (isCentInv_zc (c.card_Dl hC.sit hl))
    (c.isInvSub_img_Rl hC hδ hl) (c.card_img_Rl hC hδ hl)

theorem mem_Qv_of_comm_le_Zv_nbr (hS : Sit H M S) (hδ : vtype δ = false) {l : Geo H M}
    (hl : l ∈ nbrs δ) {x : G} (hx : x ∈ stab δ)
    (h : ⁅Vn δ, Subgroup.zpowers x⁆ ≤ Zv l) : x ∈ Qv δ := by
  have hle : commSec (Subgroup.zpowers x) (Zv δ) (Vn δ) ≤ Zv l :=
    sup_le h (Zv_le_Zv_of_nbr hS hδ hl)
  have h1 := c.img_mono hle
  rw [c.img_Zv_nbr hS hδ hl, c.img_commSec (Subgroup.zpowers_le.mpr hx), c.bar_zpowers hx] at h1
  have h2 : Nat.card (commW orth (Subgroup.zpowers (c.θ ⟨x, hx⟩)) ⊤) ≤ 2 := by
    have := Subgroup.card_le_of_le h1
    rwa [card_zpowers_vp] at this
  rcases (card_commW_zpowers_le_two_iff _).mp h2 with h3 | ⟨a, b, hab, hθ⟩
  · exact (c.ker_iff hS hδ ⟨x, hx⟩).mp h3
  · exfalso
    rw [hθ, commW_swap hab] at h1
    have h4 : ep a b ∈ Subgroup.zpowers (vp (fixPt (c.Dl l))) := h1 (Subgroup.mem_zpowers _)
    rcases (mem_zpowers_iff_of_mul_self (vp_mul_self _)).mp h4 with h5 | h5
    · exact ep_ne_one hab h5
    · exact vp_ne_ep _ hab h5.symm

end Chart

end S35.Ch

end F53.Stellmacher

end CFSG.Quasithin
