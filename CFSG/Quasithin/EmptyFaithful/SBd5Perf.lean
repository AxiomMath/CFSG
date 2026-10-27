module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.Quasithin

namespace SBd5

open scoped commutatorElement

section Perf

variable {G : Type} [Group G]

theorem mem_normalizer_commutator_of {X Y : Subgroup G} {g : G}
    (hX : g ∈ Subgroup.normalizer (X : Set G)) (hY : g ∈ Subgroup.normalizer (Y : Set G)) :
    g ∈ Subgroup.normalizer ((⁅X, Y⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
    (Subgroup.mem_normalizer_iff_map_conj_eq).mp hX, (Subgroup.mem_normalizer_iff_map_conj_eq).mp hY]

theorem commutator_eq_bot_of_double' {E Y : Subgroup G} (hE : ⁅E, E⁆ = E)
    (h : ⁅⁅Y, E⁆, E⁆ = ⊥) : ⁅Y, E⁆ = ⊥ := by
  have h1 : ⁅⁅E, Y⁆, E⁆ = ⊥ := by rw [Subgroup.commutator_comm E Y]; exact h
  have h2 := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := E) (H₂ := E) (H₃ := Y) h1 h
  rwa [hE, Subgroup.commutator_comm] at h2

theorem commutator_commutator_eq_self {W L : Subgroup G} (hperf : ⁅L, L⁆ = L)
    (hLW : L ≤ Subgroup.normalizer (W : Set G)) (hW : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) :
    ⁅⁅W, L⁆, L⁆ = ⁅W, L⁆ := by
  have hUW : ⁅W, L⁆ ≤ W := Subgroup.le_normalizer_iff_commutator_le_left.mp hLW
  have hLU : L ≤ Subgroup.normalizer ((⁅W, L⁆ : Subgroup G) : Set G) := fun g hg =>
    mem_normalizer_commutator_of (hLW hg) (Subgroup.le_normalizer hg)
  have hNU : ⁅⁅W, L⁆, L⁆ ≤ ⁅W, L⁆ := Subgroup.le_normalizer_iff_commutator_le_left.mp hLU
  refine le_antisymm hNU ?_
  set N : Subgroup G := ⁅⁅W, L⁆, L⁆ with hN
  have hLN : L ≤ Subgroup.normalizer (N : Set G) := fun g hg =>
    mem_normalizer_commutator_of (hLU hg) (Subgroup.le_normalizer hg)
  have hnW : ∀ n ∈ N, n ∈ W := fun n hn => hUW (hNU hn)
  have hWN : W ≤ Subgroup.normalizer (N : Set G) := fun w hw =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr
      (fun n hn => hW n (hnW n hn) w hw))
  let H : Subgroup G := W ⊔ L
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := sup_le hWN hLN
  have hNH : N ≤ H := fun n hn => Subgroup.mem_sup_left (hnW n hn)
  have : (N.subgroupOf H).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hHN
  let π : ↥H →* ↥H ⧸ N.subgroupOf H := QuotientGroup.mk' (N.subgroupOf H)
  let W₁ : Subgroup ↥H := W.subgroupOf H
  let L₁ : Subgroup ↥H := L.subgroupOf H
  have hmW : W₁.map H.subtype = W := Subgroup.map_subgroupOf_eq_of_le le_sup_left
  have hmL : L₁.map H.subtype = L := Subgroup.map_subgroupOf_eq_of_le le_sup_right
  have hL₁ : ⁅L₁, L₁⁆ = L₁ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_commutator, hmL, hperf]
  have hdouble : ⁅⁅W₁, L₁⁆, L₁⁆ ≤ N.subgroupOf H := by
    rw [Subgroup.subgroupOf, ← Subgroup.map_le_iff_le_comap, Subgroup.map_commutator,
      Subgroup.map_commutator, hmW, hmL]
  have hker : (N.subgroupOf H) = π.ker := (QuotientGroup.ker_mk' _).symm
  have h1 : ⁅⁅W₁.map π, L₁.map π⁆, L₁.map π⁆ = ⊥ := by
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, eq_bot_iff]
    intro x hx
    obtain ⟨z, hz, rfl⟩ := hx
    have := hdouble hz
    rw [hker] at this
    exact this
  have hperf' : ⁅L₁.map π, L₁.map π⁆ = L₁.map π := by
    rw [← Subgroup.map_commutator, hL₁]
  have h2 := commutator_eq_bot_of_double' hperf' h1
  rw [← Subgroup.map_commutator] at h2
  have h3 : ⁅W₁, L₁⁆ ≤ N.subgroupOf H := by
    rw [hker]
    intro x hx
    have : π x ∈ (⊥ : Subgroup (↥H ⧸ N.subgroupOf H)) := by
      rw [← h2]; exact ⟨x, hx, rfl⟩
    exact this
  have h4 := Subgroup.map_mono (f := H.subtype) h3
  rw [Subgroup.map_commutator, hmW, hmL, Subgroup.map_subgroupOf_eq_of_le hNH] at h4
  exact h4

end Perf

end SBd5

end CFSG.Quasithin
