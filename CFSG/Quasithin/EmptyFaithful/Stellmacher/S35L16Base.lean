module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S34Gen
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35AtFin1
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Ch2Base
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.L16

open S35.Std S35.Fin S35.At S35.Ch2
open S34 (yCommHom normal_subgroupOf_of_comm ker_comm_eq)

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

section CommImg

variable {V : Subgroup G} {y : G}

@[expose] def commImg (hV : IsMulCommutative V) (hy : y ∈ Subgroup.normalizer (V : Set G)) :
    Subgroup G :=
  (yCommHom hV hy).range.map V.subtype

omit [Finite G] in
theorem mem_commImg {hV : IsMulCommutative V} {hy : y ∈ Subgroup.normalizer (V : Set G)}
    {x : G} : x ∈ commImg hV hy ↔ ∃ a ∈ V, x = y * a * y⁻¹ * a⁻¹ := by
  constructor
  · rintro ⟨_, ⟨b, rfl⟩, rfl⟩
    exact ⟨b, b.2, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨_, ⟨⟨a, ha⟩, rfl⟩, rfl⟩

omit [Finite G] in
theorem y_mul_mem_commImg {hV : IsMulCommutative V} {hy : y ∈ Subgroup.normalizer (V : Set G)}
    {a : G} (ha : a ∈ V) : y * a * y⁻¹ * a⁻¹ ∈ commImg hV hy :=
  mem_commImg.mpr ⟨a, ha, rfl⟩

omit [Finite G] in
theorem commImg_le {hV : IsMulCommutative V} {hy : y ∈ Subgroup.normalizer (V : Set G)} :
    commImg hV hy ≤ V := by
  rintro _ ⟨b, -, rfl⟩
  exact b.2

omit [Finite G] in
theorem relIndex_commImg {C : Subgroup G} (hV : IsMulCommutative V)
    (hy : y ∈ Subgroup.normalizer (V : Set G)) (hyC : y ∈ Subgroup.normalizer (C : Set G))
    (hCV : C ≤ V) :
    (commImg hV hy ⊓ C).relIndex (commImg hV hy) = secIdx (Subgroup.zpowers y) C V := by
  have := normal_subgroupOf_of_comm hV C
  have h1 := relIndex_inf_eq_card_map (ψ := QuotientGroup.mk' (C.subgroupOf V))
    (X := V) (A := commImg hV hy) (N := C) (QuotientGroup.ker_mk' _) commImg_le
  have h2 : (commImg hV hy).subgroupOf V = (yCommHom hV hy).range := by
    unfold commImg
    exact Subgroup.comap_map_eq_self_of_injective Subtype.val_injective _
  rw [h1, h2, ← MonoidHom.range_comp]
  have hker := ker_comm_eq hV hy hyC hCV
  have h3 : secIdx (Subgroup.zpowers y) C V =
      Nat.card ((QuotientGroup.mk' (C.subgroupOf V)).comp (yCommHom hV hy)).range := by
    unfold secIdx Subgroup.relIndex
    rw [← hker, Subgroup.index_ker]
  rw [h3]

end CommImg

end S35.L16

end F53.Stellmacher

end CFSG.Quasithin
