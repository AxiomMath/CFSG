module

public import CFSG.Quasithin.Background.D2Transport
public import CFSG.Quasithin.Background.D216Sub
public import CFSG.Quasithin.Background.InternalSecAutOn

public section

namespace CFSG.Quasithin.H13.T325

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section Congr

variable {V V' : Type*} [CommGroup V] [CommGroup V'] (e : V ≃* V')

noncomputable abbrev congrHom : MulAut V →* MulAut V' := (MulAut.congr e).toMonoidHom

theorem congrHom_apply (x : MulAut V) (v : V') : congrHom e x v = e (x (e.symm v)) := rfl

theorem kq_map_congr_le [Finite V] [Finite V'] (X : Subgroup (MulAut V)) (k : ℕ) :
    kq (X.map (congrHom e)) k ≤ kq X k :=
  kq_map_mulAutCongr_le e X k

end Congr

section Restrict

variable {G : Type} [Group G] {X V VM : Subgroup G} [IsMulCommutative ↥VM]
  [IsMulCommutative ↥V]

open scoped IsMulCommutative

theorem map_autOn_le_autSub (hV : V ≤ VM) (hXV : X ≤ Subgroup.normalizer (V : Set G))
    (hXVM : X ≤ Subgroup.normalizer (VM : Set G)) :
    (autOn X V).map (congrHom (Subgroup.subgroupOfEquivOfLe hV).symm) ≤
      autSub (autOn X VM) (V.subgroupOf VM) := by
  rintro _ ⟨φ, hφ, rfl⟩
  obtain ⟨g, hgX, rfl⟩ := Setup.mem_autOn_iff.mp hφ
  have hgVM : (g : G) ∈ Subgroup.normalizer (VM : Set G) := hXVM hgX
  set ψ := conjAct VM ⟨(g : G), hgVM⟩ with hψ
  have hψs : ψ ∈ stabSub (V.subgroupOf VM) := by
    intro u
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hψ, InternalSec.coe_conjAct_apply]
    exact (Subgroup.mem_normalizer_iff.mp (hXV hgX) u).symm
  refine mem_autSub.mpr ⟨⟨ψ, hψs⟩, Setup.mem_autOn_iff.mpr ⟨⟨g, hgVM⟩, hgX, rfl⟩, ?_⟩
  ext u
  rw [resHom_apply, congrHom_apply]
  show ((ψ (u : ↥VM)) : G) = ((conjAct V g ((Subgroup.subgroupOfEquivOfLe hV) u) : ↥V) : G)
  rw [hψ, InternalSec.coe_conjAct_apply, InternalSec.coe_conjAct_apply]
  rfl

theorem qhatOf_autSub_autOn_le [Finite G] (hV : V ≤ VM) (hXV : X ≤ Subgroup.normalizer (V : Set G))
    (hXVM : X ≤ Subgroup.normalizer (VM : Set G)) :
    qhatOf (autSub (autOn X VM) (V.subgroupOf VM)) ≤ qhatOf (autOn X V) :=
  (kq_le_kq_of_le216 (map_autOn_le_autSub hV hXV hXVM) 3).trans
    (kq_map_congr_le (Subgroup.subgroupOfEquivOfLe hV).symm (autOn X V) 3)

end Restrict

end CFSG.Quasithin.H13.T325
