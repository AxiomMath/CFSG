module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.Quasithin

namespace SBd6

open scoped commutatorElement

section Gen

variable {G : Type} [Group G]

theorem commutator_eq_bot_of_double {E Y : Subgroup G} (hE : ⁅E, E⁆ = E)
    (h : ⁅⁅Y, E⁆, E⁆ = ⊥) : ⁅Y, E⁆ = ⊥ := by
  have h1 : ⁅⁅E, Y⁆, E⁆ = ⊥ := by rw [Subgroup.commutator_comm E Y]; exact h
  have h2 := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := E) (H₂ := E) (H₃ := Y) h1 h
  rwa [hE, Subgroup.commutator_comm] at h2

theorem commutator_le_of_double_le {A L N : Subgroup G} (hperf : ⁅L, L⁆ = L)
    (hAN : A ≤ Subgroup.normalizer (N : Set G)) (hLN : L ≤ Subgroup.normalizer (N : Set G))
    (h : ⁅⁅A, L⁆, L⁆ ≤ N) : ⁅A, L⁆ ≤ N := by
  let H : Subgroup G := A ⊔ L
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := sup_le hAN hLN
  have : (N.subgroupOf H).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hHN
  let π : ↥H →* ↥H ⧸ N.subgroupOf H := QuotientGroup.mk' (N.subgroupOf H)
  let A₁ : Subgroup ↥H := A.subgroupOf H
  let L₁ : Subgroup ↥H := L.subgroupOf H
  have hmA : A₁.map H.subtype = A := Subgroup.map_subgroupOf_eq_of_le le_sup_left
  have hmL : L₁.map H.subtype = L := Subgroup.map_subgroupOf_eq_of_le le_sup_right
  have hL₁ : ⁅L₁, L₁⁆ = L₁ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_commutator, hmL, hperf]
  have hdouble : ⁅⁅A₁, L₁⁆, L₁⁆ ≤ N.subgroupOf H := by
    rw [Subgroup.subgroupOf, ← Subgroup.map_le_iff_le_comap, Subgroup.map_commutator,
      Subgroup.map_commutator, hmA, hmL]
    exact h
  have hker : (N.subgroupOf H) = π.ker := (QuotientGroup.ker_mk' _).symm
  have h1 : ⁅⁅A₁.map π, L₁.map π⁆, L₁.map π⁆ = ⊥ := by
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, eq_bot_iff]
    intro x hx
    obtain ⟨z, hz, rfl⟩ := hx
    have := hdouble hz
    rw [hker] at this
    exact this
  have hperf' : ⁅L₁.map π, L₁.map π⁆ = L₁.map π := by
    rw [← Subgroup.map_commutator, hL₁]
  have h2 := commutator_eq_bot_of_double hperf' h1
  rw [← Subgroup.map_commutator] at h2
  have h3 : ⁅A₁, L₁⁆ ≤ N.subgroupOf H := by
    rw [hker]
    intro x hx
    have : π x ∈ (⊥ : Subgroup (↥H ⧸ N.subgroupOf H)) := by
      rw [← h2]; exact ⟨x, hx, rfl⟩
    exact this
  intro x hx
  have h4 := Subgroup.map_mono (f := H.subtype) h3
  rw [Subgroup.map_commutator, hmA, hmL] at h4
  obtain ⟨y, hy, rfl⟩ := h4 hx
  exact hy

end Gen

end SBd6

end CFSG.Quasithin
