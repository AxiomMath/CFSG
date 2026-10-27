module

public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.Data.Set.Card
public import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.SBd19F

theorem mul_comm_of_sq_eq_one {G : Type*} [Group G] {u v : G} (hu : u * u = 1) (hv : v * v = 1)
    (huv : (u * v) * (u * v) = 1) : u * v = v * u := by
  have e1 : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have e2 : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  calc u * v = (u * v)⁻¹ := (inv_eq_of_mul_eq_one_right huv).symm
    _ = v⁻¹ * u⁻¹ := mul_inv_rev u v
    _ = v * u := by rw [e1, e2]

theorem eq_one_of_fixed_klein {G : Type*} [Group G] {V : Subgroup G}
    (hV2 : ∀ v ∈ V, v * v = 1) (hV4 : Nat.card V = 4) {b : G}
    (hbV : ∀ v ∈ V, b * v * b⁻¹ ∈ V) (hb3 : b ^ 3 = 1) (hmove : ∃ v ∈ V, b * v ≠ v * b)
    {c : G} (hc : c ∈ V) (hbc : b * c = c * b) : c = 1 := by
  classical
  have : Finite V := Nat.finite_of_card_ne_zero (by omega)
  by_contra hc1
  have hφc : b * c * b⁻¹ = c := by rw [hbc]; group
  obtain ⟨d, hdV, hd1, hdc⟩ : ∃ d ∈ V, d ≠ 1 ∧ d ≠ c := by
    by_contra hcon
    push Not at hcon
    have hsub : (V : Set G) ⊆ {1, c} := fun d hd => by
      by_cases h1 : d = 1
      · exact Or.inl h1
      · exact Or.inr (hcon d hd h1)
    have h1 : (V : Set G).ncard ≤ ({1, c} : Set G).ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : ({1, c} : Set G).ncard ≤ 2 :=
      (Set.ncard_insert_le (1 : G) {c}).trans (by simp)
    have h3 : (V : Set G).ncard = 4 := by rw [← Nat.card_coe_set_eq]; exact hV4
    omega
  have hcdV : c * d ∈ V := V.mul_mem hc hdV
  have hcc : c * c = 1 := hV2 c hc
  have hdd : d * d = 1 := hV2 d hdV
  have hcom : c * d = d * c := mul_comm_of_sq_eq_one hcc hdd (hV2 _ hcdV)
  have hcd1 : c * d ≠ 1 := by
    intro h
    have h' : c = d⁻¹ := mul_eq_one_iff_eq_inv.mp h
    rw [inv_eq_of_mul_eq_one_right hdd] at h'
    exact hdc h'.symm
  have hcdc : c * d ≠ c := fun h => hd1 (by simpa using h)
  have hcdd : c * d ≠ d := fun h => hc1 (by simpa using h)
  have hV : ∀ v ∈ V, v = 1 ∨ v = c ∨ v = d ∨ v = c * d := by
    have hn1 : (1 : G) ∉ ({c, d, c * d} : Finset G) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hc1 h.symm, fun h => hd1 h.symm, fun h => hcd1 h.symm⟩
    have hn2 : c ∉ ({d, c * d} : Finset G) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hdc h.symm, fun h => hcdc h.symm⟩
    have hn3 : d ∉ ({c * d} : Finset G) := by
      simp only [Finset.mem_singleton]
      exact fun h => hcdd h.symm
    have hfin : (({1, c, d, c * d} : Finset G) : Set G).ncard = 4 := by
      rw [Set.ncard_coe_finset, Finset.card_insert_of_notMem hn1,
        Finset.card_insert_of_notMem hn2, Finset.card_insert_of_notMem hn3, Finset.card_singleton]
    have hsub : (({1, c, d, c * d} : Finset G) : Set G) ⊆ (V : Set G) := by
      intro v hv
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl | rfl | rfl
      exacts [V.one_mem, hc, hdV, hcdV]
    have h4 : (V : Set G).ncard = 4 := by rw [← Nat.card_coe_set_eq]; exact hV4
    have heq := Set.eq_of_subset_of_ncard_le hsub (by omega) (Set.toFinite _)
    intro v hv
    have : v ∈ (({1, c, d, c * d} : Finset G) : Set G) := by rw [heq]; exact hv
    simpa using this
  have hbd : b * d * b⁻¹ ∈ V := hbV d hdV
  have hbd1 : b * d * b⁻¹ ≠ 1 := fun h => hd1 (by
    have := congrArg (fun z => b⁻¹ * z * b) h
    simpa [mul_assoc] using this)
  have hbdc : b * d * b⁻¹ ≠ c := fun h => hdc (by
    have h' : b * d * b⁻¹ = b * c * b⁻¹ := h.trans hφc.symm
    have := congrArg (fun z => b⁻¹ * z * b) h'
    simpa [mul_assoc] using this)
  rcases hV _ hbd with h | h | h | h
  · exact hbd1 h
  · exact hbdc h
  ·
    obtain ⟨v, hvV, hv⟩ := hmove
    apply hv
    have hbd' : b * d = d * b := by
      have := congrArg (fun z => z * b) h
      simpa [mul_assoc] using this
    rcases hV v hvV with rfl | rfl | rfl | rfl
    · simp
    · exact hbc
    · exact hbd'
    · calc b * (c * d) = (b * c) * d := by rw [mul_assoc]
        _ = (c * b) * d := by rw [hbc]
        _ = c * (b * d) := by rw [mul_assoc]
        _ = c * (d * b) := by rw [hbd']
        _ = (c * d) * b := by rw [mul_assoc]
  ·
    have hb3' : b * b * b = 1 := by rw [← pow_three', hb3]
    have h3 : b * (b * (b * d * b⁻¹) * b⁻¹) * b⁻¹ = d := by
      have : b * (b * (b * d * b⁻¹) * b⁻¹) * b⁻¹ = (b * b * b) * d * (b * b * b)⁻¹ := by group
      rw [this, hb3']
      group
    rw [h] at h3
    have h4 : b * (c * d) * b⁻¹ = c * (c * d) := by
      calc b * (c * d) * b⁻¹ = (b * c * b⁻¹) * (b * d * b⁻¹) := by group
        _ = c * (c * d) := by rw [hφc, h]
    have h5 : c * (c * d) = d := by rw [← mul_assoc, hcc, one_mul]
    rw [h4, h5, h] at h3
    exact hcdd h3

theorem sq_eq_one_of_lift {L : Type*} [Group L] {Z : Subgroup L} (hZc : Z ≤ Subgroup.center L)
    (hZ2 : ∀ z ∈ Z, z * z = 1)
    (hconj : ∀ y₁ y₂ : L, y₁ * y₁ ∈ Z → y₂ * y₂ ∈ Z → y₁ ∉ Z → y₂ ∉ Z →
      ∃ g : L, ∃ z ∈ Z, g * y₁ * g⁻¹ = y₂ * z)
    (β : L ≃* L) (hβZ : ∀ z : L, β z ∈ Z ↔ z ∈ Z) (hβ : ∀ z ∈ Z, β z = z → z = 1)
    (y : L) (hy : y * y ∈ Z) : y * y = 1 := by
  by_cases hyZ : y ∈ Z
  · exact hZ2 y hyZ
  have hβyZ : β y ∉ Z := fun h => hyZ ((hβZ y).mp h)
  have hβsq : β y * β y ∈ Z := by
    rw [← map_mul]
    exact (hβZ _).mpr hy
  obtain ⟨g, z, hz, hgz⟩ := hconj y (β y) hy hβsq hyZ hβyZ
  have hyc : g * (y * y) * g⁻¹ = y * y := by
    rw [Subgroup.mem_center_iff.mp (hZc hy) g]
    group
  have e1 : (g * y * g⁻¹) * (g * y * g⁻¹) = y * y := by
    rw [← hyc]
    group
  have hzc : β y * z = z * β y := Subgroup.mem_center_iff.mp (hZc hz) (β y)
  have e2 : (β y * z) * (β y * z) = β (y * y) := by
    calc (β y * z) * (β y * z) = β y * (z * β y) * z := by group
      _ = β y * (β y * z) * z := by rw [hzc]
      _ = β y * β y * (z * z) := by group
      _ = β (y * y) := by rw [hZ2 z hz, mul_one, map_mul]
  have e3 : β (y * y) = y * y := by rw [← e2, ← hgz, e1]
  exact hβ _ hy e3

end CFSG.Quasithin.SBd19F
