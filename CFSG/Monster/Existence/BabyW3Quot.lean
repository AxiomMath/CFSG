module

public import CFSG.Monster.Existence.BabyW3Count
public import Mathlib.Data.ZMod.QuotientGroup

public section

namespace CFSG.Monster.Existence

variable {G H : Type*} [Group G] [Group H]

theorem eq_one_or_eq_of_mem_zpowers_sq {z g : G} (hz2 : z * z = 1) (h : g ∈ Subgroup.zpowers z) :
    g = 1 ∨ g = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 h
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
  · left
    rw [hm, zpow_mul, zpow_two, hz2, one_zpow]
  · right
    rw [hm, zpow_add_one, zpow_mul, zpow_two, hz2, one_zpow, one_mul]

theorem centralizer_card_of_central_quotient (κ : G →* H) (hκ : Function.Surjective κ) {z : G}
    (hz : z ∈ Subgroup.center G) (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hker : κ.ker = Subgroup.zpowers z) (y : G) :
    ∃ o : ℕ, 1 ≤ o ∧ o ≤ 2 ∧ (o = 2 → ∃ c : G, c * y * c⁻¹ = z * y) ∧
      2 * Nat.card ↥(Subgroup.centralizer ({κ y} : Set H)) =
        o * Nat.card ↥(Subgroup.centralizer ({y} : Set G)) := by
  have hzc : ∀ g : G, g * z = z * g := fun g => Subgroup.mem_center_iff.1 hz g
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hκz : κ z = 1 := by
    rw [← MonoidHom.mem_ker, hker]
    exact Subgroup.mem_zpowers z
  have hconj1 : ∀ a b : G, a * b * y * (a * b)⁻¹ = a * (b * y * b⁻¹) * a⁻¹ := fun a b => by group
  have hconj2 : ∀ a : G, a * (z * y) * a⁻¹ = z * (a * y * a⁻¹) := fun a => by
    calc a * (z * y) * a⁻¹ = (a * z) * y * a⁻¹ := by group
      _ = (z * a) * y * a⁻¹ := by rw [hzc a]
      _ = z * (a * y * a⁻¹) := by group
  obtain ⟨P, hmem⟩ : ∃ P : Subgroup G, ∀ c : G, c ∈ P ↔ c * y * c⁻¹ = y ∨ c * y * c⁻¹ = z * y :=
    ⟨{ carrier := {c | c * y * c⁻¹ = y ∨ c * y * c⁻¹ = z * y}
       one_mem' := Or.inl (by simp)
       mul_mem' := by
         intro a b ha hb
         rcases ha with ha | ha <;> rcases hb with hb | hb
         · exact Or.inl (by rw [hconj1, hb, ha])
         · exact Or.inr (by rw [hconj1, hb, hconj2, ha])
         · exact Or.inr (by rw [hconj1, hb, ha])
         · exact Or.inl (by rw [hconj1, hb, hconj2, ha, ← mul_assoc, hz2, one_mul])
       inv_mem' := by
         intro a ha
         rcases ha with ha | ha
         · left
           have hay : a * y = y * a := mul_inv_eq_iff_eq_mul.1 ha
           show a⁻¹ * y * a⁻¹⁻¹ = y
           rw [inv_inv]
           calc a⁻¹ * y * a = a⁻¹ * (y * a) * a⁻¹ * a := by group
             _ = a⁻¹ * (a * y) * a⁻¹ * a := by rw [hay]
             _ = y := by group
         · right
           have h1 : a⁻¹ * (z * y) * a = y := by
             calc a⁻¹ * (z * y) * a = a⁻¹ * (a * y * a⁻¹) * a := by rw [ha]
               _ = y := by group
           have h2 := hconj2 a⁻¹
           rw [inv_inv] at h2
           show a⁻¹ * y * a⁻¹⁻¹ = z * y
           rw [inv_inv]
           calc a⁻¹ * y * a = z * (z * (a⁻¹ * y * a)) := by rw [← mul_assoc, hz2, one_mul]
             _ = z * y := by rw [← h2, h1] }, fun c => Iff.rfl⟩
  have hCP : Subgroup.centralizer ({y} : Set G) ≤ P := by
    intro c hc
    rw [hmem]
    left
    have := Subgroup.mem_centralizer_singleton_iff.1 hc
    calc c * y * c⁻¹ = y * c * c⁻¹ := by rw [← this]
      _ = y := by group
  have hzP : z ∈ P := by
    rw [hmem]
    left
    calc z * y * z⁻¹ = y * z * z⁻¹ := by rw [← hzc y]
      _ = y := by group
  have hZP : Subgroup.zpowers z ≤ P := Subgroup.zpowers_le.2 hzP
  have hrange : (κ.comp P.subtype).range = Subgroup.centralizer ({κ y} : Set H) := by
    ext w
    simp only [MonoidHom.mem_range, MonoidHom.comp_apply, Subgroup.coe_subtype,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨⟨c, hc⟩, rfl⟩
      rcases (hmem c).1 hc with h | h
      · have hcy : c * y = y * c := mul_inv_eq_iff_eq_mul.1 h
        show κ c * κ y = κ y * κ c
        rw [← map_mul, ← map_mul, hcy]
      · have hcy : c * y = z * y * c := mul_inv_eq_iff_eq_mul.1 h
        show κ c * κ y = κ y * κ c
        rw [← map_mul, ← map_mul, hcy, map_mul, map_mul, hκz, one_mul, map_mul]
    · intro hw
      obtain ⟨c, rfl⟩ := hκ w
      have h1 : κ (c * y * c⁻¹ * y⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hw]
        group
      have h2 : c * y * c⁻¹ * y⁻¹ ∈ Subgroup.zpowers z := by
        rw [← hker]
        exact h1
      refine ⟨⟨c, (hmem c).2 ?_⟩, rfl⟩
      rcases eq_one_or_eq_of_mem_zpowers_sq hz2 h2 with h | h
      · exact Or.inl (mul_inv_eq_one.1 h)
      · right
        calc c * y * c⁻¹ = c * y * c⁻¹ * y⁻¹ * y := by group
          _ = z * y := by rw [h]
  have hkerP : (κ.comp P.subtype).ker = (Subgroup.zpowers z).subgroupOf P := by
    ext c
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hker, MonoidHom.mem_ker]
    rfl
  have hord : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  have hkercard : Nat.card (κ.comp P.subtype).ker = 2 := by
    rw [hkerP, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZP).toEquiv, Nat.card_zpowers, hord]
  have hP2 : 2 * Nat.card ↥(Subgroup.centralizer ({κ y} : Set H)) = Nat.card P := by
    have h := Subgroup.card_ker_mul_card_range (κ.comp P.subtype)
    rw [hkercard, hrange] at h
    exact h
  have horb := ncard_conj_mul_natCard_inf_centralizer P y
  rw [inf_eq_right.2 hCP] at horb
  have hsub : {u : G | ∃ g ∈ P, u = g⁻¹ * y * g} ⊆ {y, z * y} := by
    rintro _ ⟨g, hg, rfl⟩
    have h := (hmem g⁻¹).1 (P.inv_mem hg)
    rw [inv_inv] at h
    exact h
  have hfin : {u : G | ∃ g ∈ P, u = g⁻¹ * y * g}.Finite := (Set.toFinite _).subset hsub
  refine ⟨{u : G | ∃ g ∈ P, u = g⁻¹ * y * g}.ncard, ?_, ?_, ?_, ?_⟩
  · exact (Set.ncard_pos hfin).2 ⟨y, 1, P.one_mem, by simp⟩
  · calc {u : G | ∃ g ∈ P, u = g⁻¹ * y * g}.ncard ≤ ({y, z * y} : Set G).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ ({z * y} : Set G).ncard + 1 := Set.ncard_insert_le _ _
      _ = 2 := by rw [Set.ncard_singleton]
  · intro h2
    by_contra hno
    push Not at hno
    have hsub' : {u : G | ∃ g ∈ P, u = g⁻¹ * y * g} ⊆ {y} := by
      rintro _ ⟨g, hg, rfl⟩
      have h := (hmem g⁻¹).1 (P.inv_mem hg)
      rw [inv_inv] at h
      rcases h with h | h
      · exact h
      · exfalso
        apply hno g⁻¹
        rw [inv_inv]
        exact h
    have := Set.ncard_le_ncard hsub' (Set.toFinite _)
    rw [Set.ncard_singleton, h2] at this
    omega
  · rw [hP2, horb]

end CFSG.Monster.Existence
