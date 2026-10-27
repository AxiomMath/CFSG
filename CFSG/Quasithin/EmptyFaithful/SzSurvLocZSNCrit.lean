module

public import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.SzSurvLoc

variable {G : Type*} [Group G]

theorem inv_mul_mem_of_relIndex_two {Q S : Subgroup G} (h2 : Q.relIndex S = 2) {g h : G}
    (hg : g ∈ S) (hh : h ∈ S) (hgQ : g ∉ Q) (hhQ : h ∉ Q) : h⁻¹ * g ∈ Q := by
  have h2' : (Q.subgroupOf S).index = 2 := h2
  have key : (⟨h, hh⟩ : ↥S)⁻¹ * ⟨g, hg⟩ ∈ Q.subgroupOf S := by
    rw [Subgroup.mul_mem_iff_of_index_two h2']
    constructor
    · intro h1
      exact absurd (inv_mem_iff.mp (Subgroup.mem_subgroupOf.mp h1)) hhQ
    · intro h1
      exact absurd (Subgroup.mem_subgroupOf.mp h1) hgQ
  exact Subgroup.mem_subgroupOf.mp key

theorem commutator_mem_of_critical_pair {S Q A Zs : Subgroup G}
    (hQ2 : Q.relIndex S = 2) (hAQ : ∀ q ∈ Q, ∀ a ∈ A, q * a = a * q) {k : G}
    (hAk : ∀ a ∈ A, k⁻¹ * a * k ∈ S) {v y x : G} (hv : v ∈ A) (hy : y ∈ A)
    (hx : x = k * y * k⁻¹) (hxS : x ∈ S) (hxQ : x ∉ Q) (hvx : v * x ≠ x * v)
    (hZ : v * x * v⁻¹ * x⁻¹ ∈ Zs) :
    ∀ s ∈ S, ∀ a ∈ A, s * a * s⁻¹ * a⁻¹ ∈ Zs := by
  have hconj : ∀ q ∈ Q, (k * q * k⁻¹) * x = x * (k * q * k⁻¹) := by
    intro q hq
    have h1 := hAQ q hq y hy
    rw [hx]
    calc k * q * k⁻¹ * (k * y * k⁻¹) = k * (q * y) * k⁻¹ := by group
      _ = k * (y * q) * k⁻¹ := by rw [h1]
      _ = k * y * k⁻¹ * (k * q * k⁻¹) := by group
  have key : ∀ a ∈ A, a * x * a⁻¹ * x⁻¹ ∈ Zs := by
    intro a ha
    have hg : k⁻¹ * a * k ∈ S := hAk a ha
    have hh : k⁻¹ * v * k ∈ S := hAk v hv
    have hhQ : k⁻¹ * v * k ∉ Q := by
      intro hQ
      apply hvx
      have h1 := hconj _ hQ
      have e : k * (k⁻¹ * v * k) * k⁻¹ = v := by group
      rw [e] at h1
      exact h1
    by_cases haQ : k⁻¹ * a * k ∈ Q
    · have h1 := hconj _ haQ
      have e : k * (k⁻¹ * a * k) * k⁻¹ = a := by group
      rw [e] at h1
      have h2 : a * x * a⁻¹ * x⁻¹ = 1 := by
        calc a * x * a⁻¹ * x⁻¹ = (a * x) * a⁻¹ * x⁻¹ := rfl
          _ = (x * a) * a⁻¹ * x⁻¹ := by rw [h1]
          _ = 1 := by group
      rw [h2]
      exact Zs.one_mem
    · have hq : (k⁻¹ * v * k)⁻¹ * (k⁻¹ * a * k) ∈ Q :=
        inv_mul_mem_of_relIndex_two hQ2 hg hh haQ hhQ
      have hqc := hconj _ hq
      have haw : a = v * (k * ((k⁻¹ * v * k)⁻¹ * (k⁻¹ * a * k)) * k⁻¹) := by group
      have h2 : a * x * a⁻¹ * x⁻¹ = v * x * v⁻¹ * x⁻¹ := by
        generalize hw : k * ((k⁻¹ * v * k)⁻¹ * (k⁻¹ * a * k)) * k⁻¹ = w at hqc haw
        rw [haw]
        calc v * w * x * (v * w)⁻¹ * x⁻¹ = v * (w * x) * w⁻¹ * v⁻¹ * x⁻¹ := by group
          _ = v * (x * w) * w⁻¹ * v⁻¹ * x⁻¹ := by rw [hqc]
          _ = v * x * v⁻¹ * x⁻¹ := by group
      rw [h2]
      exact hZ
  intro s hs a ha
  by_cases hsQ : s ∈ Q
  · have h1 := hAQ s hsQ a ha
    have h2 : s * a * s⁻¹ * a⁻¹ = 1 := by
      calc s * a * s⁻¹ * a⁻¹ = (s * a) * s⁻¹ * a⁻¹ := rfl
        _ = (a * s) * s⁻¹ * a⁻¹ := by rw [h1]
        _ = 1 := by group
    rw [h2]
    exact Zs.one_mem
  · have hq : x⁻¹ * s ∈ Q := inv_mul_mem_of_relIndex_two hQ2 hs hxS hsQ hxQ
    have hqa := hAQ _ hq a ha
    have hs' : s = x * (x⁻¹ * s) := by group
    have h2 : s * a * s⁻¹ * a⁻¹ = (a * x * a⁻¹ * x⁻¹)⁻¹ := by
      generalize hq' : x⁻¹ * s = q at hqa hs'
      rw [hs']
      calc x * q * a * (x * q)⁻¹ * a⁻¹ = x * (q * a) * q⁻¹ * x⁻¹ * a⁻¹ := by group
        _ = x * (a * q) * q⁻¹ * x⁻¹ * a⁻¹ := by rw [hqa]
        _ = x * a * x⁻¹ * a⁻¹ := by group
        _ = (a * x * a⁻¹ * x⁻¹)⁻¹ := by group
    rw [h2]
    exact Zs.inv_mem (key a ha)

end CFSG.Quasithin.SzSurvLoc
