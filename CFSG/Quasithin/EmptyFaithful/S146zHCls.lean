module

public import CFSG.Quasithin.EmptyFaithful.S14612ED

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.LieType.BorelTits CFSG.Quasithin.C1Pack
open scoped commutatorElement

section Cls

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H : Subgroup G}

@[expose] def clsU (h : HypF91 T V L V₁ Vp H) {u : G} (hu : u ∈ conjClosure Vp H) : UMod h :=
  IntMod.mk h.isElemAbelian_tilde
    ⟨secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨u, U_le_normalizer h hu⟩, secMk_mem_secImg hu⟩

theorem clsU_val (h : HypF91 T V L V₁ Vp H) {u : G} (hu : u ∈ conjClosure Vp H) :
    (clsU h hu).val = secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨u, U_le_normalizer h hu⟩ := rfl

theorem clsU_congr (h : HypF91 T V L V₁ Vp H) {u u' : G} (hu : u ∈ conjClosure Vp H)
    (hu' : u' ∈ conjClosure Vp H) (e : u = u') : clsU h hu = clsU h hu' := by
  subst e
  rfl

theorem exists_clsU (h : HypF91 T V L V₁ Vp H) (w : UMod h) :
    ∃ u : G, ∃ hu : u ∈ conjClosure Vp H, clsU h hu = w := by
  obtain ⟨⟨u, huN⟩, hu, huw⟩ := mem_secImg.mp w.val_mem
  exact ⟨u, hu, IntMod.val_injective huw⟩

theorem clsU_mul (h : HypF91 T V L V₁ Vp H) {u u' : G} (hu : u ∈ conjClosure Vp H)
    (hu' : u' ∈ conjClosure Vp H) :
    clsU h hu * clsU h hu' = clsU h ((conjClosure Vp H).mul_mem hu hu') := by
  apply IntMod.val_injective
  rw [IntMod.val_mul, clsU_val, clsU_val, clsU_val, ← map_mul]
  rfl

theorem clsU_one (h : HypF91 T V L V₁ Vp H) :
    clsU h ((conjClosure Vp H).one_mem) = 1 := by
  apply IntMod.val_injective
  rw [clsU_val, IntMod.val_one]
  exact secMk_eq_one_iff.mpr V₁.one_mem

theorem clsU_inv (h : HypF91 T V L V₁ Vp H) {u : G} (hu : u ∈ conjClosure Vp H) :
    (clsU h hu)⁻¹ = clsU h ((conjClosure Vp H).inv_mem hu) := by
  apply IntMod.val_injective
  rw [IntMod.val_inv, clsU_val, clsU_val, ← map_inv]
  rfl

theorem clsU_eq_iff (h : HypF91 T V L V₁ Vp H) {u u' : G} (hu : u ∈ conjClosure Vp H)
    (hu' : u' ∈ conjClosure Vp H) : clsU h hu = clsU h hu' ↔ u⁻¹ * u' ∈ V₁ := by
  constructor
  · intro e
    have := congrArg IntMod.val e
    rw [clsU_val, clsU_val] at this
    exact secMk_eq_secMk_iff.mp this
  · intro e
    apply IntMod.val_injective
    rw [clsU_val, clsU_val]
    exact secMk_eq_secMk_iff.mpr e

theorem clsU_eq_one_iff (h : HypF91 T V L V₁ Vp H) {u : G} (hu : u ∈ conjClosure Vp H) :
    clsU h hu = 1 ↔ u ∈ V₁ := by
  constructor
  · intro e
    have := congrArg IntMod.val e
    rw [clsU_val, IntMod.val_one] at this
    exact secMk_eq_one_iff.mp this
  · intro e
    apply IntMod.val_injective
    rw [clsU_val, IntMod.val_one]
    exact secMk_eq_one_iff.mpr e

omit [Finite G] in
theorem conj_mem_UH {y u : G} (hy : y ∈ H) (hu : u ∈ conjClosure Vp H) :
    y * u * y⁻¹ ∈ conjClosure Vp H :=
  (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure Vp H hy) u).mp hu

theorem rhoH_clsU (h : HypF91 T V L V₁ Vp H) (y : ↥H) {u : G} (hu : u ∈ conjClosure Vp H) :
    rhoH h y (clsU h hu) = clsU h (conj_mem_UH y.2 hu) := by
  apply IntMod.val_injective
  rw [rhoH_val]
  simp only [clsU_val]
  have e : (⟨(y : G) * u * (y : G)⁻¹, U_le_normalizer h (conj_mem_UH y.2 hu)⟩ :
      ↥(Subgroup.normalizer (V₁ : Set G))) =
      Subgroup.inclusion h.H_normalizes_V₁ y * ⟨u, U_le_normalizer h hu⟩ *
        (Subgroup.inclusion h.H_normalizes_V₁ y)⁻¹ := Subtype.ext rfl
  rw [e, map_mul, map_mul, map_inv]

theorem rhoH_clsU_eq_iff (h : HypF91 T V L V₁ Vp H) (y : ↥H) {u : G} (hu : u ∈ conjClosure Vp H) :
    rhoH h y (clsU h hu) = clsU h hu ↔ (y : G) * u * (y : G)⁻¹ * u⁻¹ ∈ V₁ := by
  rw [rhoH_clsU, clsU_eq_iff]
  have hu1 : u⁻¹ ∈ Subgroup.normalizer (V₁ : Set G) :=
    (Subgroup.normalizer (V₁ : Set G)).inv_mem (U_le_normalizer h hu)
  have key := Subgroup.mem_normalizer_iff.mp hu1 ((y : G) * u * (y : G)⁻¹ * u⁻¹)⁻¹
  have e : u⁻¹ * ((y : G) * u * (y : G)⁻¹ * u⁻¹)⁻¹ * u⁻¹⁻¹ = ((y : G) * u * (y : G)⁻¹)⁻¹ * u := by
    group
  rw [e] at key
  exact key.symm.trans (Subgroup.inv_mem_iff V₁)

end Cls

end CFSG.Quasithin
