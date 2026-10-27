module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.Finite

public section

namespace CFSG.Sporadic.SuzRecog.LocalR

open Subgroup

variable {G H : Type*} [Group G] [Group H] {z : G}
  (σ : ↥(centralizer ({z} : Set G)) ≃* H)

@[expose] def trS (K : Subgroup G) : Subgroup H :=
  (K.subgroupOf (centralizer ({z} : Set G))).map σ.toMonoidHom

variable {σ}

theorem mem_trS_iff {K : Subgroup G} {y : H} :
    y ∈ trS σ K ↔ ((σ.symm y : ↥(centralizer ({z} : Set G))) : G) ∈ K := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : (x : G) ∈ K := mem_subgroupOf.1 hx
    simpa using hx'
  · intro hy
    exact ⟨σ.symm y, mem_subgroupOf.2 hy, by simp⟩

theorem mem_trS {K : Subgroup G} {x : G} (hx : x ∈ centralizer ({z} : Set G)) :
    σ ⟨x, hx⟩ ∈ trS σ K ↔ x ∈ K := by
  rw [mem_trS_iff, MulEquiv.symm_apply_apply]

theorem card_trS {K : Subgroup G} (hK : K ≤ centralizer ({z} : Set G)) :
    Nat.card (trS σ K) = Nat.card K := by
  rw [trS, Subgroup.card_map_of_injective σ.injective,
    Nat.card_congr (subgroupOfEquivOfLe hK).toEquiv]

theorem trS_mono {K L : Subgroup G} (h : K ≤ L) : trS σ K ≤ trS σ L := fun y hy => by
  rw [mem_trS_iff] at hy ⊢
  exact h hy

theorem trS_inf (K L : Subgroup G) : trS σ (K ⊓ L) = trS σ K ⊓ trS σ L := by
  ext y
  simp only [mem_trS_iff, mem_inf]

theorem trS_sup {K L : Subgroup G} (hK : K ≤ centralizer ({z} : Set G))
    (hL : L ≤ centralizer ({z} : Set G)) : trS σ (K ⊔ L) = trS σ K ⊔ trS σ L := by
  rw [trS, trS, trS, subgroupOf_sup hK hL, Subgroup.map_sup]

theorem trS_centralizer_singleton {x : G} (hx : x ∈ centralizer ({z} : Set G)) :
    trS σ (centralizer ({x} : Set G)) = centralizer ({σ ⟨x, hx⟩} : Set H) := by
  ext y
  rw [mem_trS_iff, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' : σ.symm y * ⟨x, hx⟩ = ⟨x, hx⟩ * σ.symm y := Subtype.ext h
    have := congrArg σ h'
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at this
  · intro h
    have := congrArg σ.symm h
    rw [map_mul, map_mul, MulEquiv.symm_apply_apply] at this
    exact congrArg Subtype.val this

theorem trS_centralizer {K : Subgroup G} (hK : K ≤ centralizer ({z} : Set G)) :
    trS σ (centralizer (K : Set G)) = centralizer (trS σ K : Set H) := by
  ext y
  rw [mem_trS_iff, mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro h w hw
    rw [SetLike.mem_coe, mem_trS_iff] at hw
    have h1 := h _ hw
    have h2 : σ.symm w * σ.symm y = σ.symm y * σ.symm w := Subtype.ext h1
    have := congrArg σ h2
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this
  · intro h k hk
    have hw : σ ⟨k, hK hk⟩ ∈ trS σ K := (mem_trS (hK hk)).2 hk
    have h1 := h _ hw
    have := congrArg σ.symm h1
    rw [map_mul, map_mul, MulEquiv.symm_apply_apply] at this
    exact congrArg Subtype.val this

end CFSG.Sporadic.SuzRecog.LocalR
