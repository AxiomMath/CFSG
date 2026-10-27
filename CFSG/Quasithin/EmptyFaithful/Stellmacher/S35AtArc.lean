module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ChSyl
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35AtFin1
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.At

open S35.Std S35.Fin

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

@[expose] def ArcDict (H M : Subgroup G) : Prop :=
  ∀ (δ l ε : Geo H M) (c : Ch.Chart δ), vtype δ = false → l ∈ nbrs δ → ε ∈ nbrs l → ε ≠ δ →
    c.img (Vn δ ⊓ Vn ε) = commW orth (Subgroup.zpowers (zc (c.Dl l))) ⊤ ∧
      c.img (Zv l) = Subgroup.zpowers (vp (fixPt (c.Dl l)))

theorem Zv_le_Vn_inf (hS : Sit H M S) {δ l ε : Geo H M} (hδ : vtype δ = false)
    (hl : l ∈ nbrs δ) (hε : ε ∈ nbrs l) : Zv δ ≤ Vn δ ⊓ Vn ε :=
  le_inf (Zv_le_Vn_S5 hS hδ)
    ((S34.Zv_le_Zv_nbr hS.glob hδ hl).trans (Zv_le_Vn (mem_nbrs_symm.mp hε)))

theorem Arc.thm (hS : Sit H M S) (hA : ArcDict H M) {δ l ε : Geo H M} (c : Ch.Chart δ)
    (hδ : vtype δ = false) (hl : l ∈ nbrs δ) (hε : ε ∈ nbrs l) (hne : ε ≠ δ) {x : G}
    (hx : x ∈ stab δ ⊓ stab l) (hcen : ∀ r ∈ Vn δ ⊓ Vn ε, x * r * x⁻¹ = r) :
    c.θ ⟨x, hx.1⟩ ∈ That (c.Dl l) ∧ ∀ u ∈ Vn δ, ⁅u, x⁆ ∈ Vn δ ⊓ Vn ε := by
  have hD : Nat.card (c.Dl l) = 8 := c.card_Dl hS hl
  obtain ⟨hplane, -⟩ := hA δ l ε c hδ hl hε hne
  have h1 : c.θ ⟨x, hx.1⟩ ∈ cenW (commW orth (Subgroup.zpowers (zc (c.Dl l))) ⊤) := by
    rw [← hplane]
    intro w hw
    obtain ⟨r, hr, rfl⟩ := (c.mem_img_iff').mp hw
    refine (c.comm_mem_iff ⟨x, hx.1⟩ r).mp ?_
    have := hcen r hr
    have e : x * (r : G) * x⁻¹ * (r : G)⁻¹ = 1 := by rw [this]; simp
    show x * (r : G) * x⁻¹ * (r : G)⁻¹ ∈ Zv δ
    rw [e]
    exact (Zv δ).one_mem
  have h2 : c.θ ⟨x, hx.1⟩ ∈ c.Dl l := c.mem_bar_of_mem hx hx.1
  have hT : c.θ ⟨x, hx.1⟩ ∈ That (c.Dl l) := cenW_commW_inf_le_That hD ⟨h1, h2⟩
  refine ⟨hT, fun u hu => ?_⟩
  have hxs : Subgroup.zpowers x ≤ stab δ := Subgroup.zpowers_le.mpr hx.1
  have hZ := Zv_le_Vn_inf hS hδ hl hε
  have hcs : c.img (commSec (Subgroup.zpowers x) (Zv δ) (Vn δ)) ≤ c.img (Vn δ ⊓ Vn ε) := by
    rw [c.img_commSec hxs, hplane, c.bar_zpowers hx.1]
    exact commW_le_of_le_That hD (Subgroup.zpowers_le.mpr hT)
  have hle := (c.img_le_img_iff' hZ (c.commSec_le_Vn hxs)).mp hcs
  have hux : ⁅u, x⁆ ∈ ⁅Vn δ, Subgroup.zpowers x⁆ :=
    Subgroup.commutator_mem_commutator hu (Subgroup.mem_zpowers x)
  exact hle (le_sup_left (a := ⁅Vn δ, Subgroup.zpowers x⁆) hux)

omit [Finite G] in
theorem relIndex_preθ {δ : Geo H M} (c : Ch.Chart δ) {A : Subgroup G} (hA : A ≤ stab δ)
    (D : Subgroup (Perm (Fin 5))) : (c.preθ D).relIndex A = D.relIndex (c.bar A) := by
  have e1 : (c.preθ D).subgroupOf (stab δ) = D.comap c.θ := by
    ext x
    rw [Subgroup.mem_subgroupOf, c.mem_preθ_iff]
    rfl
  rw [← Subgroup.relIndex_subgroupOf hA (H := c.preθ D), e1, Subgroup.relIndex_comap]
  rfl

omit [Finite G] in
theorem isPGroup_bar {δ : Geo H M} (c : Ch.Chart δ) {A : Subgroup G} (hA : A ≤ stab δ)
    (h : IsPGroup 2 A) : IsPGroup 2 (c.bar A) := by
  have h1 : IsPGroup 2 (A.subgroupOf (stab δ)) :=
    h.of_equiv (Subgroup.subgroupOfEquivOfLe hA).symm
  exact h1.map c.θ


end S35.At

end F53.Stellmacher

end CFSG.Quasithin
