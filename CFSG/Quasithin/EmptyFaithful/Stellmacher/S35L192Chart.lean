module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Ch2Lat2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin10
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std4
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Stmt2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.L192

open S35.Std S35.II S35.Fin S35.Ch2
open S34 (Cb)

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {β α' : Geo H M}

variable (c : Chart2 β)

include c

omit [Finite G] in
theorem img_sup_Cb' {U : Subgroup G} (hUV : U ≤ Vn β) : c.img (U ⊔ Cb β) = c.img U := by
  apply le_antisymm
  · have h : U ⊔ Cb β ≤ c.pre (c.img U) :=
      sup_le ((c.le_pre_iff hUV).mpr le_rfl) (c.Cb_le_pre _)
    calc c.img (U ⊔ Cb β) ≤ c.img (c.pre (c.img U)) := c.img_mono h
      _ = c.img U := c.img_pre _
  · exact c.img_mono le_sup_left

omit [Finite G] in
theorem bar_sup' {A B : Subgroup G} (hA : A ≤ stab β) (hB : B ≤ stab β) :
    c.bar (A ⊔ B) = c.bar A ⊔ c.bar B := by
  unfold S35.Ch2.Chart2.bar
  rw [Subgroup.subgroupOf_sup hA hB, Subgroup.map_sup]

theorem bar_eq_bot_of_le_Qv (hS : Sit H M S) (hβ : vtype β = false) {A : Subgroup G}
    (hA : A ≤ Qv β) : c.bar A = ⊥ := by
  rw [eq_bot_iff]
  intro σ hσ
  obtain ⟨a, ha, rfl⟩ := (c.mem_bar_iff).mp hσ
  exact (c.ker_iff hS hβ a).mpr (hA ha)

theorem isQuad_bar' (hS : Sit H M S) (hp : S34.PD β α') : IsQuad (c.bar (Vn α')) := by
  have hle : Vn α' ≤ stab β := (Std.PD_Vn_le_stab hS hp).2
  intro a ha w hw
  obtain ⟨u, hu, rfl⟩ := (c.mem_bar_iff).mp ha
  rw [← c.img_commSec hle] at hw
  have hcs : commSec (Vn α') (Cb β) (Vn β) = ⁅Vn β, Vn α'⁆ ⊔ Cb β := rfl
  rw [hcs, img_sup_Cb' c ((PD_comm_le hS hp).trans inf_le_left)] at hw
  obtain ⟨r, hr, rfl⟩ := (c.mem_img_iff').mp hw
  refine (c.comm_mem_iff u r).mp ?_
  have h1 : ⁅(r : G), (u : G)⁆ ∈ ⁅⁅Vn β, Vn α'⁆, Vn α'⁆ :=
    Subgroup.commutator_mem_commutator hr hu
  rw [(PD_quadratic hS hp).2, Subgroup.mem_bot] at h1
  have h2 : (r : G) * u = u * r := commutatorElement_eq_one_iff_mul_comm.mp h1
  have : (u : G) * r * (u : G)⁻¹ * (r : G)⁻¹ = 1 := by
    rw [← h2]; group
  rw [this]
  exact (Cb β).one_mem

theorem isElemAb_bar' (hS : Sit H M S) (α' : Geo H M) :
    IsElemAb (c.bar (Vn α')) := by
  have hE := Std.Vn_isElemAbelian hS α'
  refine ⟨fun a ha => ?_, fun a ha b hb => ?_⟩
  · obtain ⟨u, hu, rfl⟩ := (c.mem_bar_iff).mp ha
    rw [← map_mul]
    have h2 : (u : G) ^ 2 = 1 := F7.isElemAbelian_pow_eq_one hE hu
    have : u * u = 1 := Subtype.ext (by rw [Subgroup.coe_mul, ← pow_two, h2]; rfl)
    rw [this, map_one]
  · obtain ⟨u, hu, rfl⟩ := (c.mem_bar_iff).mp ha
    obtain ⟨v, hv, rfl⟩ := (c.mem_bar_iff).mp hb
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (F7.isElemAbelian_comm hE hu hv)

omit [Finite G] in
theorem secIdx_eq_two_iff (hRk : RkZvEq H M) (hβ : vtype β = false) {x : G} (hx : x ∈ stab β) :
    secIdx (Subgroup.zpowers x) (Zv β) (Vn β) = 2 ↔ (c.θ ⟨x, hx⟩).IsSwap := by
  rw [hRk β hβ x hx]
  unfold S34.rk
  rw [c.secIdx_eq_idx hx]
  exact idx_orth_eq_two_iff _

end S35.L192

end F53.Stellmacher

end CFSG.Quasithin
