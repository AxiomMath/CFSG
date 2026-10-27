module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS.K7

variable {G : Type} [Group G] [Finite G]

abbrev stab (E : Subgroup G) (v : G) : Subgroup G := E ⊓ Subgroup.centralizer {v}

omit [Finite G] in
theorem mem_stab {E : Subgroup G} {v y : G} : y ∈ stab E v ↔ y ∈ E ∧ y * v * y⁻¹ = v := by
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [h2]; group⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    calc y * v = y * v * y⁻¹ * y := by group
      _ = v * y := by rw [h2]

noncomputable abbrev orb (E : Subgroup G) (v : G) : Finset G := by
  classical
  exact (Set.toFinite (Set.range fun y : ↥E => (y : G) * v * (y : G)⁻¹)).toFinset

theorem mem_orb {E : Subgroup G} {v w : G} : w ∈ orb E v ↔ ∃ y ∈ E, y * v * y⁻¹ = w := by
  classical
  simp only [orb, Set.Finite.mem_toFinset, Set.mem_range, Subtype.exists, exists_prop]

omit [Finite G] in
theorem stab_conj {E : Subgroup G} (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) {g v : G} (hg : g ∈ E) :
    stab E (g * v * g⁻¹) = stab E v := by
  ext e
  rw [mem_stab, mem_stab]
  refine and_congr_right fun he => ?_
  have hc := hEc e he g hg
  constructor
  · intro h
    have : g * (e * v * e⁻¹) * g⁻¹ = g * v * g⁻¹ := by
      calc g * (e * v * e⁻¹) * g⁻¹ = (g * e) * v * (g * e)⁻¹ := by group
        _ = (e * g) * v * (e * g)⁻¹ := by rw [hc]
        _ = e * (g * v * g⁻¹) * e⁻¹ := by group
        _ = g * v * g⁻¹ := h
    have := congrArg (fun x => g⁻¹ * x * g) this
    simpa [mul_assoc] using this
  · intro h
    calc e * (g * v * g⁻¹) * e⁻¹ = (e * g) * v * (e * g)⁻¹ := by group
      _ = (g * e) * v * (g * e)⁻¹ := by rw [hc]
      _ = g * (e * v * e⁻¹) * g⁻¹ := by group
      _ = g * v * g⁻¹ := by rw [h]

theorem disjoint_orb {E : Subgroup G} (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) {v w : G}
    (h : stab E v ≠ stab E w) : Disjoint (orb E v) (orb E w) := by
  rw [Finset.disjoint_left]
  intro x hxv hxw
  obtain ⟨y, hy, rfl⟩ := mem_orb.mp hxv
  obtain ⟨y', hy', e⟩ := mem_orb.mp hxw
  apply h
  rw [← stab_conj hEc hy (v := v), ← stab_conj hEc hy' (v := w), e]

theorem three_le_card_orb {E : Subgroup G} (hE3 : ∀ y ∈ E, y ^ 3 = 1) {v y : G} (hy : y ∈ E)
    (hyv : y ∉ stab E v) : 3 ≤ (orb E v).card := by
  classical
  have h1 : y * v * y⁻¹ ≠ v := fun h => hyv (mem_stab.mpr ⟨hy, h⟩)
  have hy2 : y ^ 2 * v * (y ^ 2)⁻¹ ≠ v := by
    intro h
    apply hyv
    refine mem_stab.mpr ⟨hy, ?_⟩
    have hy4 : y = y ^ 2 * y ^ 2 := by
      calc y = y ^ 3 * y := by rw [hE3 y hy, one_mul]
        _ = y ^ 2 * y ^ 2 := by group
    rw [hy4]
    calc y ^ 2 * y ^ 2 * v * (y ^ 2 * y ^ 2)⁻¹ = y ^ 2 * (y ^ 2 * v * (y ^ 2)⁻¹) * (y ^ 2)⁻¹ := by
          group
      _ = v := by rw [h, h]
  have h12 : y ^ 2 * v * (y ^ 2)⁻¹ ≠ y * v * y⁻¹ := by
    intro h
    apply h1
    calc y * v * y⁻¹ = y⁻¹ * (y ^ 2 * v * (y ^ 2)⁻¹) * y := by group
      _ = y⁻¹ * (y * v * y⁻¹) * y := by rw [h]
      _ = v := by group
  have hsub : ({v, y * v * y⁻¹, y ^ 2 * v * (y ^ 2)⁻¹} : Finset G) ⊆ orb E v := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact mem_orb.mpr ⟨1, E.one_mem, by group⟩
    · exact mem_orb.mpr ⟨y, hy, rfl⟩
    · exact mem_orb.mpr ⟨y ^ 2, E.pow_mem hy 2, rfl⟩
  have hc : ({v, y * v * y⁻¹, y ^ 2 * v * (y ^ 2)⁻¹} : Finset G).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [h1.symm, hy2.symm]),
      Finset.card_insert_of_notMem (by simp [h12.symm]), Finset.card_singleton]
  exact hc ▸ Finset.card_le_card hsub

theorem orb_subset {E Y : Subgroup G} (hEY : E ≤ Subgroup.normalizer (Y : Set G)) {v : G}
    (hv : v ∈ Y) : orb E v ⊆ (Set.toFinite (Y : Set G)).toFinset := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := mem_orb.mp hx
  rw [Set.Finite.mem_toFinset]
  exact (Subgroup.mem_normalizer_iff.mp (hEY hy) v).mp hv

theorem one_notMem_orb {E : Subgroup G} {v : G} (hv : v ≠ 1) : (1 : G) ∉ orb E v := by
  intro h
  obtain ⟨y, -, hy⟩ := mem_orb.mp h
  apply hv
  calc v = y⁻¹ * (y * v * y⁻¹) * y := by group
    _ = 1 := by rw [hy]; group

end CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS.K7
