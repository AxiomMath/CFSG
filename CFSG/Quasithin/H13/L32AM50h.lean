module

public import CFSG.Quasithin.H13.L32AM50b

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

@[expose] noncomputable def vHat (V H W : Subgroup G) [IsMulCommutative ↥(conjClosure V H)] :
    Subgroup (Hat V H W) :=
  (V.subgroupOf (conjClosure V H)).map (InternalSec.secMk (W.subgroupOf (conjClosure V H)))

namespace TopW

variable {W : Subgroup G} (C : TopW T L V H W) [IsMulCommutative ↥(conjClosure V H)]
include C

omit [IsMulCommutative ↥(conjClosure V H)] in
theorem sup_le_U : V ⊔ W ≤ conjClosure V H := sup_le (le_conjClosure V H) C.hWU'

theorem mk_mem_vHat_iff (u : ↥(conjClosure V H)) :
    InternalSec.secMk (W.subgroupOf (conjClosure V H)) u ∈ vHat V H W ↔ (u : G) ∈ V ⊔ W := by
  constructor
  · rintro ⟨a, ha, hau⟩
    have h1 : InternalSec.secMk (W.subgroupOf (conjClosure V H)) (a⁻¹ * u) = 1 := by
      rw [map_mul, map_inv, hau, inv_mul_cancel]
    rw [A6.A6Mod.secMk_eq_one_iff] at h1
    have e : (u : G) = a * (a⁻¹ * u : ↥(conjClosure V H)) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp ha))
      (Subgroup.mem_sup_right h1)
  · intro hu
    have hu' : u ∈ V.subgroupOf (conjClosure V H) ⊔ W.subgroupOf (conjClosure V H) := by
      rw [← Subgroup.subgroupOf_sup (le_conjClosure V H) C.hWU', Subgroup.mem_subgroupOf]
      exact hu
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hu'
    refine ⟨a, ha, ?_⟩
    have hb1 : InternalSec.secMk (W.subgroupOf (conjClosure V H)) b = 1 :=
      (A6.A6Mod.secMk_eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mp hb)
    rw [map_mul, hb1, mul_one]

theorem act_mk (h : ↥H) (u : ↥(conjClosure V H)) :
    C.act h (InternalSec.secMk (W.subgroupOf (conjClosure V H)) u) =
      InternalSec.secMk (W.subgroupOf (conjClosure V H))
        ⟨(h : G) * u * (h : G)⁻¹, (Subgroup.mem_normalizer_iff.mp
          (le_normalizer_conjClosure V H h.2) u).mp u.2⟩ := by
  rw [C.act_secMk]
  congr 1

theorem mem_normalizer_iff (h : ↥H) :
    (h : G) ∈ Subgroup.normalizer ((V ⊔ W : Subgroup G) : Set G) ↔
      ∀ x ∈ vHat V H W, C.act h x ∈ vHat V H W ∧ C.act h⁻¹ x ∈ vHat V H W := by
  have hU := C.sup_le_U
  have key : ∀ g : ↥H, ∀ u : ↥(conjClosure V H),
      (C.act g (InternalSec.secMk (W.subgroupOf (conjClosure V H)) u) ∈ vHat V H W ↔
        (g : G) * u * (g : G)⁻¹ ∈ V ⊔ W) := by
    intro g u
    rw [C.act_mk, C.mk_mem_vHat_iff]
  constructor
  · intro hN x hx
    obtain ⟨u, hu, rfl⟩ := hx
    have huW : (u : G) ∈ V ⊔ W := Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hu)
    refine ⟨(key h u).mpr ((Subgroup.mem_normalizer_iff.mp hN u).mp huW), ?_⟩
    have hN' : ((h⁻¹ : ↥H) : G) ∈ Subgroup.normalizer ((V ⊔ W : Subgroup G) : Set G) := by
      rw [Subgroup.coe_inv]
      exact inv_mem hN
    exact (key h⁻¹ u).mpr ((Subgroup.mem_normalizer_iff.mp hN' u).mp huW)
  · intro hst
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have hyU := hU hy
      have h1 := (hst _ ((C.mk_mem_vHat_iff ⟨y, hyU⟩).mpr hy)).1
      exact (key h ⟨y, hyU⟩).mp h1
    · intro hy
      have hyU := hU hy
      have h1 := (hst _ ((C.mk_mem_vHat_iff ⟨_, hyU⟩).mpr hy)).2
      have h2 := (key h⁻¹ ⟨_, hyU⟩).mp h1
      rwa [Subgroup.coe_inv, inv_inv, show (h : G)⁻¹ * ((h : G) * y * (h : G)⁻¹) * (h : G) = y by
        group] at h2

end TopW

end CFSG.Quasithin.H13.L32A.C
