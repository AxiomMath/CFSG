module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Ch2Plane
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ChThat

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

theorem mem_That2_iff (hS : Sit H M S) {δ l : Geo H M} {x : G} :
    x ∈ That2 δ l ↔ x ∈ stab δ ⊓ stab l ∧ ∀ r ∈ Plane2 δ l, x * r * x⁻¹ * r⁻¹ ∈ Zv δ :=
  F53B3.N37.mem_cSecIn_iff (inf_le_left.trans (stab_le_normalizer_Zv hS.glob.amalg δ))

theorem That2_le_inf (hS : Sit H M S) (δ l : Geo H M) : That2 δ l ≤ stab δ ⊓ stab l :=
  fun _ hx => ((mem_That2_iff hS).mp hx).1

theorem Qv_le_That2 (hS : Sit H M S) {δ l : Geo H M} (hδ : vtype δ = false) (hl : l ∈ nbrs δ) :
    Qv δ ≤ That2 δ l := fun _ hq =>
  (mem_That2_iff hS).mpr ⟨Qv_le_inf' hS hl hq, fun _ hr =>
    comm_mem_Zv_of_Qv hS hδ hq (Plane2_le_Vn hS hδ l hr)⟩

namespace Chart2

variable {δ : Geo H M} (c : Chart2 δ)

include c

theorem θ_mem_That_of_mem_That2 (hS : Sit H M S) (hδ : vtype δ = false) {l : Geo H M}
    (hl : l ∈ nbrs δ) {x : G} (hx : x ∈ That2 δ l) :
    c.θ ⟨x, ((mem_That2_iff hS).mp hx).1.1⟩ ∈ That (c.Dl l) := by
  have hD := c.card_Dl hS hl
  obtain ⟨hxi, hxr⟩ := (mem_That2_iff hS).mp hx
  rw [← cenW_commW_z hD (isCentInv_zc hD), mem_cenW, ← c.img_Plane2 hS hδ hl]
  intro w hw
  obtain ⟨r, hr, rfl⟩ := (c.mem_img_iff').mp hw
  exact (c.comm_mem_iff ⟨x, hxi.1⟩ r).mp (S34.Zv_le_Cb hS.glob hδ (hxr r hr))

theorem That2_le_preθ (hS : Sit H M S) (hδ : vtype δ = false) {l : Geo H M} (hl : l ∈ nbrs δ) :
    That2 δ l ≤ c.preθ (That (c.Dl l)) := fun x hx =>
  (c.mem_preθ_iff ⟨x, ((mem_That2_iff hS).mp hx).1.1⟩).mpr
    (c.θ_mem_That_of_mem_That2 hS hδ hl hx)

theorem bar_That2_le (hS : Sit H M S) (hδ : vtype δ = false) {l : Geo H M} (hl : l ∈ nbrs δ) :
    c.bar (That2 δ l) ≤ That (c.Dl l) := by
  rintro _ ⟨x, hx, rfl⟩
  exact c.θ_mem_That_of_mem_That2 hS hδ hl hx

theorem comm_mem_Cb_of_mem_That (hS : Sit H M S) (hδ : vtype δ = false) {l : Geo H M}
    (hl : l ∈ nbrs δ) {x : G} (hx : x ∈ stab δ) (hθ : c.θ ⟨x, hx⟩ ∈ That (c.Dl l)) {r : G}
    (hr : r ∈ Plane2 δ l) : x * r * x⁻¹ * r⁻¹ ∈ Cb δ := by
  have hD := c.card_Dl hS hl
  have h1 := cenW_commW_z hD (isCentInv_zc hD)
  rw [← h1, mem_cenW, ← c.img_Plane2 hS hδ hl] at hθ
  have hrV := Plane2_le_Vn hS hδ l hr
  exact (c.comm_mem_iff ⟨x, hx⟩ ⟨r, hrV⟩).mpr
    (hθ _ ((c.mem_img_iff').mpr ⟨⟨r, hrV⟩, hr, rfl⟩))

theorem That2_eq_preθ (hS : Sit H M S) (hδ : vtype δ = false) (hU : UC δ) {l : Geo H M}
    (hl : l ∈ nbrs δ) : That2 δ l = c.preθ (That (c.Dl l)) := by
  apply le_antisymm (c.That2_le_preθ hS hδ hl)
  intro x hx
  have hxs : x ∈ stab δ := c.preθ_le_stab _ hx
  have hθ := (c.mem_preθ_iff ⟨x, hxs⟩).mp hx
  have hxi : x ∈ stab δ ⊓ stab l := by
    rw [← c.preθ_Dl hS hδ hl]
    exact (c.mem_preθ_iff ⟨x, hxs⟩).mpr (That_le _ hθ)
  refine (mem_That2_iff hS).mpr ⟨hxi, fun r hr => ?_⟩
  have h1 := c.comm_mem_Cb_of_mem_That hS hδ hl hxs hθ hr
  have h2 : x * r * x⁻¹ * r⁻¹ ∈ Plane2 δ l := by
    have := (Subgroup.mem_normalizer_iff.mp (inf_le_normalizer_Plane2 hS δ l hxi) r).mp hr
    exact (Plane2 δ l).mul_mem this ((Plane2 δ l).inv_mem hr)
  exact hU.Plane2_inf_le hS hδ l ⟨h2, h1⟩

theorem mem_That2_iff_θ (hS : Sit H M S) (hδ : vtype δ = false) (hU : UC δ) {l : Geo H M}
    (hl : l ∈ nbrs δ) {x : G} (hx : x ∈ stab δ ⊓ stab l) :
    x ∈ That2 δ l ↔ c.θ ⟨x, hx.1⟩ ∈ That (c.Dl l) := by
  rw [c.That2_eq_preθ hS hδ hU hl, c.mem_preθ_iff ⟨x, hx.1⟩]

theorem bar_That2 (hS : Sit H M S) (hδ : vtype δ = false) (hU : UC δ) {l : Geo H M}
    (hl : l ∈ nbrs δ) : c.bar (That2 δ l) = That (c.Dl l) := by
  rw [c.That2_eq_preθ hS hδ hU hl, c.bar_preθ]

theorem relIndex_That2 (hS : Sit H M S) (hδ : vtype δ = false) (hU : UC δ) {l : Geo H M}
    (hl : l ∈ nbrs δ) : (That2 δ l).relIndex (stab δ ⊓ stab l) = 2 := by
  have hD := c.card_Dl hS hl
  have hQ := Qv_le_That2 hS hδ hl
  have h1 := c.card_bar hS hδ (A := stab δ ⊓ stab l) inf_le_left (Qv_le_inf' hS hl)
  have h2 := c.card_bar hS hδ (A := That2 δ l)
    ((That2_le_inf hS δ l).trans inf_le_left) hQ
  rw [c.bar_That2 hS hδ hU hl, S35.Ch.card_That hD] at h2
  have h3 : Nat.card (c.bar (stab δ ⊓ stab l)) = 8 := hD
  have h4 := Subgroup.relIndex_mul_relIndex (Qv δ) (That2 δ l) (stab δ ⊓ stab l)
    hQ (That2_le_inf hS δ l)
  rw [← h1, ← h2, h3] at h4
  omega

theorem comm_mem_Plane2_sup (hS : Sit H M S) (hδ : vtype δ = false) {l : Geo H M}
    (hl : l ∈ nbrs δ) {x : G} (hx : x ∈ stab δ) (hθ : c.θ ⟨x, hx⟩ ∈ That (c.Dl l)) {u : G}
    (hu : u ∈ Vn δ) : x * u * x⁻¹ * u⁻¹ ∈ Plane2 δ l ⊔ Cb δ := by
  have hD := c.card_Dl hS hl
  have hxD : c.θ ⟨x, hx⟩ ∈ c.Dl l := That_le _ hθ
  have h1 := (trivOn_commW_z_iff hD (isCentInv_zc hD) hxD).mpr hθ (c.π ⟨u, hu⟩)
  have hP : c.img (Plane2 δ l ⊔ Cb δ) = commW orth (Subgroup.zpowers (zc (c.Dl l))) ⊤ := by
    rw [c.img_sup_Cb (Plane2_le_Vn hS hδ l), c.img_Plane2 hS hδ hl]
  rw [← hP] at h1
  exact (c.mem_img_iff le_sup_right (conjV ⟨x, hx⟩ ⟨u, hu⟩ * ⟨u, hu⟩⁻¹)).mp
    (by rw [map_mul, map_inv, c.π_conj]; exact h1)

theorem comm_mem_Plane2 (hS : Sit H M S) (hδ : vtype δ = false) (hU : UC δ) {l : Geo H M}
    (hl : l ∈ nbrs δ) {x : G} (hx : x ∈ That2 δ l) {u : G} (hu : u ∈ Vn δ) :
    x * u * x⁻¹ * u⁻¹ ∈ Plane2 δ l := by
  have hxs : x ∈ stab δ := ((mem_That2_iff hS).mp hx).1.1
  have h := c.comm_mem_Plane2_sup hS hδ hl hxs (c.θ_mem_That_of_mem_That2 hS hδ hl hx) hu
  have hle : Plane2 δ l ≤ Subgroup.normalizer (Cb δ : Set G) :=
    (Plane2_le_Vn hS hδ l).trans c.Vn_le_normalizer_Cb
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right (Plane2 δ l) (Cb δ) hle
  have h' : x * u * x⁻¹ * u⁻¹ ∈ (↑(Plane2 δ l ⊔ Cb δ) : Set G) := h
  rw [hmul] at h'
  obtain ⟨p, hp, d, hd, hpd⟩ := h'
  have hcomm : x * u * x⁻¹ * u⁻¹ ∈ ⁅Vn δ, stab δ⁆ := by
    have h1 : ⁅u, x⁆ ∈ ⁅Vn δ, stab δ⁆ := Subgroup.commutator_mem_commutator hu hxs
    have h2 : ⁅u, x⁆⁻¹ ∈ ⁅Vn δ, stab δ⁆ := (⁅Vn δ, stab δ⁆).inv_mem h1
    have : ⁅u, x⁆⁻¹ = x * u * x⁻¹ * u⁻¹ := by rw [commutatorElement_def]; group
    rwa [this] at h2
  have hdZ : d ∈ Zv δ := by
    have hd' : d = p⁻¹ * (x * u * x⁻¹ * u⁻¹) := by rw [← hpd]; group
    refine hU.sup_inf_le hS hδ ⟨?_, hd⟩
    rw [hd']
    exact (⁅Vn δ, stab δ⁆ ⊔ Zv δ).mul_mem ((⁅Vn δ, stab δ⁆ ⊔ Zv δ).inv_mem
      (Plane2_le_comm_sup δ l hp)) (Subgroup.mem_sup_left hcomm)
  rw [← hpd]
  exact (Plane2 δ l).mul_mem hp (Zv_le_Plane2 δ l hdZ)

theorem commutator_le_Plane2 (hS : Sit H M S) (hδ : vtype δ = false) (hU : UC δ) {l : Geo H M}
    (hl : l ∈ nbrs δ) {K : Subgroup G} (hK : K ≤ That2 δ l) : ⁅Vn δ, K⁆ ≤ Plane2 δ l := by
  rw [Subgroup.commutator_le]
  intro u hu x hx
  have h := c.comm_mem_Plane2 hS hδ hU hl (hK hx) hu
  have : ⁅u, x⁆ = (x * u * x⁻¹ * u⁻¹)⁻¹ := by
    rw [commutatorElement_def]; group
  rw [this]
  exact (Plane2 δ l).inv_mem h

theorem relIndex_Cb_Plane2 (hS : Sit H M S) (hδ : vtype δ = false) {l : Geo H M}
    (hl : l ∈ nbrs δ) : (Cb δ).relIndex (Plane2 δ l) = 4 := by
  rw [← c.card_img' (Plane2_le_Vn hS hδ l), c.img_Plane2 hS hδ hl]
  exact card_commW_z (c.card_Dl hS hl) (isCentInv_zc (c.card_Dl hS hl))

theorem relIndex_Zv_Plane2 (hS : Sit H M S) (hδ : vtype δ = false) (hU : UC δ) {l : Geo H M}
    (hl : l ∈ nbrs δ) : (Zv δ).relIndex (Plane2 δ l) = 4 := by
  have h1 : Cb δ ⊓ Plane2 δ l = Zv δ := by
    apply le_antisymm
    · intro x hx
      exact hU.Plane2_inf_le hS hδ l ⟨hx.2, hx.1⟩
    · exact le_inf (S34.Zv_le_Cb hS.glob hδ) (Zv_le_Plane2 δ l)
  rw [← c.relIndex_Cb_Plane2 hS hδ hl, ← Subgroup.inf_relIndex_right (Cb δ) (Plane2 δ l), h1]

end Chart2

end S35.Ch2

end F53.Stellmacher

end CFSG.Quasithin
