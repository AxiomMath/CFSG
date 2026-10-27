module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ChCent
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin7

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

@[expose] def Tcen (δ l : Geo H M) : Subgroup G := cSecIn (stab δ ⊓ stab l) (Zv δ) (Rl δ l)

theorem mem_Tcen_iff (hS : Sit H M S) {δ l : Geo H M} {x : G} :
    x ∈ Tcen δ l ↔ x ∈ stab δ ⊓ stab l ∧ ∀ r ∈ Rl δ l, x * r * x⁻¹ * r⁻¹ ∈ Zv δ :=
  F53B3.N37.mem_cSecIn_iff
    (inf_le_left.trans (stab_le_normalizer_Zv hS.glob.amalg δ))

theorem card_That {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) : Nat.card (That D) = 4 := by
  obtain ⟨g, rfl⟩ := exists_cj hD
  rw [← cj_That, That_std, card_cj]
  exact card_S5That_eq_four

theorem Tcen_le_inf (hS : Sit H M S) (δ l : Geo H M) : Tcen δ l ≤ stab δ ⊓ stab l :=
  fun _ hx => ((mem_Tcen_iff hS).mp hx).1

namespace Chart

variable {δ : Geo H M} (c : Chart δ)

include c

theorem mem_Tcen_iff_θ (hC : Ctx H M S) (hδ : vtype δ = false) {l : Geo H M} (hl : l ∈ nbrs δ)
    {x : G} (hx : x ∈ stab δ ⊓ stab l) :
    x ∈ Tcen δ l ↔ c.θ ⟨x, hx.1⟩ ∈ That (c.Dl l) := by
  have hD := c.card_Dl hC.sit hl
  have hcen := cenW_commW_z hD (isCentInv_zc hD)
  rw [mem_Tcen_iff hC.sit, ← hcen, mem_cenW, ← c.img_Rl hC hδ hl]
  simp only [hx, true_and]
  constructor
  · intro h w hw
    obtain ⟨r, hr, rfl⟩ := (c.mem_img_iff').mp hw
    exact (c.comm_mem_iff ⟨x, hx.1⟩ r).mp (h r hr)
  · intro h r hr
    have hrV : r ∈ Vn δ := hC.Rl_le_Vn hδ hl hr
    exact (c.comm_mem_iff ⟨x, hx.1⟩ ⟨r, hrV⟩).mpr (h _ ((c.mem_img_iff').mpr ⟨⟨r, hrV⟩, hr, rfl⟩))

theorem comm_mem_Rl_of_mem_Tcen (hC : Ctx H M S) (hδ : vtype δ = false) {l : Geo H M}
    (hl : l ∈ nbrs δ) {x : G} (hx : x ∈ Tcen δ l) {u : G} (hu : u ∈ Vn δ) :
    x * u * x⁻¹ * u⁻¹ ∈ Rl δ l := by
  have hD := c.card_Dl hC.sit hl
  have hxi : x ∈ stab δ ⊓ stab l := Tcen_le_inf hC.sit δ l hx
  have hθ := (c.mem_Tcen_iff_θ hC hδ hl hxi).mp hx
  have hθD : c.θ ⟨x, hxi.1⟩ ∈ c.Dl l := c.mem_bar_of_mem hxi hxi.1
  have h1 := (trivOn_commW_z_iff hD (isCentInv_zc hD) hθD).mpr hθ (c.π ⟨u, hu⟩)
  rw [← c.img_Rl hC hδ hl] at h1
  have hconj : (⟨x * u * x⁻¹ * u⁻¹, (Vn δ).mul_mem (conj_mem_Vn hxi.1 hu) ((Vn δ).inv_mem hu)⟩ :
      ↥(Vn δ)) = conjV ⟨x, hxi.1⟩ ⟨u, hu⟩ * ⟨u, hu⟩⁻¹ := rfl
  have h2 := (c.mem_img_iff (hC.Zv_le_Rl hδ hl) (conjV ⟨x, hxi.1⟩ ⟨u, hu⟩ * ⟨u, hu⟩⁻¹)).mp
    (by rw [map_mul, map_inv, c.π_conj]; exact h1)
  exact h2

end Chart

end S35.Ch

end F53.Stellmacher

end CFSG.Quasithin
