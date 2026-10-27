module

public import Mathlib.GroupTheory.Coxeter.Inversion
import CFSG.LocalAnalysis.StandardType.GGF4A3ResidualRep
import CFSG.LocalAnalysis.StandardType.GGF4OrigRep

public section

namespace CFSG.StandardType

open CFSG.StandardType.F4Model

private theorem closure_eq_top_of_subset_eq_top {W : Type} [Group W] {S T : Set W}
    (hST : S ⊆ T) (hS : Subgroup.closure S = ⊤) : Subgroup.closure T = ⊤ := by
  rw [eq_top_iff, ← hS]
  exact Subgroup.closure_mono hST

private theorem mem_all_of_order_three_of_closure_ne_top {W : Type} [Group W] {R : F4Rep W}
    {a b : Fin 3 → W} {H : Fin 3 → Subgroup W}
    (hH_order : ∀ t t', R.IsRefl t → R.IsRefl t' → orderOf (t * t') = 3 →
      (∀ j, t ∈ H j ∧ t' ∈ H j) ∨
        Subgroup.closure ({a 0, a 1, a 2, t, t'} : Set W) = ⊤)
    (hRb : ∀ i, R.IsRefl (b i)) (hb01 : orderOf (b 0 * b 1) = 3)
    (hHab : Subgroup.closure (Set.range a ∪ Set.range b) ≠ ⊤) :
    ∀ j, b 0 ∈ H j ∧ b 1 ∈ H j := by
  intro j
  rcases hH_order (b 0) (b 1) (hRb 0) (hRb 1) hb01 with h | h
  · exact h j
  · exfalso
    have hsub : ({a 0, a 1, a 2, b 0, b 1} : Set W) ⊆ Set.range a ∪ Set.range b := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp
    exact hHab (closure_eq_top_of_subset_eq_top hsub h)

private theorem order_of_mul_eq_four_of_a3_core {W : Type} [Group W] {R : F4Rep W}
    {a b c : Fin 3 → W} {H : Fin 3 → Subgroup W}
    (hH_ne : ∀ j, H j ≠ ⊤) (hHa : ∀ i j, a i ∈ H j)
    (hHb : ∀ j, b 0 ∈ H j ∧ b 1 ∈ H j)
    (hHc : ∀ j, c 0 ∈ H j ∧ c 1 ∈ H j)
    (hH_exists : ∀ t, R.IsRefl t → ∃ j, t ∈ H j)
    (hH_order : ∀ t t', R.IsRefl t → R.IsRefl t' → orderOf (t * t') = 3 →
      (∀ j, t ∈ H j ∧ t' ∈ H j) ∨
        Subgroup.closure ({a 0, a 1, a 2, t, t'} : Set W) = ⊤)
    (hRb : ∀ i, R.IsRefl (b i)) (hRc : ∀ i, R.IsRefl (c i))
    (hb12 : orderOf (b 1 * b 2) = 3 ∨ orderOf (b 1 * b 2) = 4)
    (hHab : Subgroup.closure (Set.range a ∪ Set.range b) ≠ ⊤)
    (hHabC : Subgroup.closure (Set.range a ∪ Set.range b ∪ Set.range c) = ⊤) :
    orderOf (b 1 * b 2) = 4 := by
  rcases hb12 with h3 | h4
  · exfalso
    have hb2H : ∀ j, b 2 ∈ H j := by
      intro j
      rcases hH_order (b 1) (b 2) (hRb 1) (hRb 2) h3 with h | h
      · exact (h j).2
      · exfalso
        have hsub : ({a 0, a 1, a 2, b 1, b 2} : Set W) ⊆ Set.range a ∪ Set.range b := by
          intro x hx
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp
        exact hHab (closure_eq_top_of_subset_eq_top hsub h)
    obtain ⟨j₀, hc2H⟩ := hH_exists (c 2) (hRc 2)
    have hsubset : Set.range a ∪ Set.range b ∪ Set.range c ⊆ (H j₀ : Set W) := by
      intro x hx
      simp only [Set.mem_union, Set.mem_range] at hx
      rcases hx with (⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩
      · exact hHa i j₀
      · rcases (by decide : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2) i with rfl | rfl | rfl
        · exact (hHb j₀).1
        · exact (hHb j₀).2
        · exact hb2H j₀
      · rcases (by decide : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2) i with rfl | rfl | rfl
        · exact (hHc j₀).1
        · exact (hHc j₀).2
        · exact hc2H
    have hle : Subgroup.closure (Set.range a ∪ Set.range b ∪ Set.range c) ≤ H j₀ :=
      (Subgroup.closure_le (H j₀)).mpr hsubset
    rw [hHabC] at hle
    exact (hH_ne j₀) (eq_top_iff.mpr hle)
  · exact h4

theorem ggF4A3Residual_endpoints {W : Type} [Group W] (cs : CoxeterSystem CoxeterMatrix.F₄ W)
    {a b c : Fin 3 → W} (ha : ∀ i, cs.IsReflection (a i)) (hb : ∀ i, cs.IsReflection (b i))
    (hc : ∀ i, cs.IsReflection (c i)) (ha01 : orderOf (a 0 * a 1) = 3)
    (ha12 : orderOf (a 1 * a 2) = 3) (ha02 : orderOf (a 0 * a 2) = 2)
    (hb01 : orderOf (b 0 * b 1) = 3) (hb12 : orderOf (b 1 * b 2) = 3 ∨ orderOf (b 1 * b 2) = 4)
    (hb02 : orderOf (b 0 * b 2) = 2) (hc01 : orderOf (c 0 * c 1) = 3)
    (hc12 : orderOf (c 1 * c 2) = 3 ∨ orderOf (c 1 * c 2) = 4)
    (hab : Subgroup.closure (Set.range a ∪ Set.range b) ≠ ⊤)
    (hac : Subgroup.closure (Set.range a ∪ Set.range c) ≠ ⊤)
    (habc : Subgroup.closure (Set.range a ∪ Set.range b ∪ Set.range c) = ⊤) :
    orderOf (b 1 * b 2) = 4 ∧ orderOf (c 1 * c 2) = 4 ∧
      Subgroup.closure (Set.range b ∪ Set.range c) = ⊤ := by
  obtain ⟨R, hRs⟩ := exists_f4Rep cs
  have hRa : ∀ i, R.IsRefl (a i) := fun i => (F4Rep.isRefl_iff hRs).2 (ha i)
  have hRb : ∀ i, R.IsRefl (b i) := fun i => (F4Rep.isRefl_iff hRs).2 (hb i)
  have hRc : ∀ i, R.IsRefl (c i) := fun i => (F4Rep.isRefl_iff hRs).2 (hc i)
  obtain ⟨H, hH_ne, hHa, hH_exists, hH_order⟩ :=
    R.a3_core (a := a) hRa ha01 ha12 ha02
  have hbH : ∀ j, b 0 ∈ H j ∧ b 1 ∈ H j :=
    mem_all_of_order_three_of_closure_ne_top hH_order hRb hb01 hab
  have hcH : ∀ j, c 0 ∈ H j ∧ c 1 ∈ H j :=
    mem_all_of_order_three_of_closure_ne_top hH_order hRc hc01 hac
  have hb12_eq : orderOf (b 1 * b 2) = 4 :=
    order_of_mul_eq_four_of_a3_core hH_ne hHa hbH hcH hH_exists hH_order
      hRb hRc hb12 hab habc
  have hHabC' : Subgroup.closure (Set.range a ∪ Set.range c ∪ Set.range b) = ⊤ := by
    rw [Set.union_right_comm]
    exact habc
  have hc12_eq : orderOf (c 1 * c 2) = 4 :=
    order_of_mul_eq_four_of_a3_core (b := c) (c := b) hH_ne hHa hcH hbH hH_exists hH_order
      hRc hRb hc12 hac hHabC'
  obtain ⟨H', hH'_ne, hbH', hH'_cases⟩ :=
    R.core_of_rep (a := b) hRb hb01 hb12_eq hb02
  have haH' : ∀ i, a i ∈ H' := by
    intro i
    rcases hH'_cases (a i) (hRa i) with h | h
    · exact h
    · exfalso
      have hsub : ({b 0, b 1, b 2, a i} : Set W) ⊆ Set.range a ∪ Set.range b := by
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl | rfl <;> simp
      exact hab (closure_eq_top_of_subset_eq_top hsub h)
  have hBC : Subgroup.closure (Set.range b ∪ Set.range c) = ⊤ := by
    by_contra hne
    have hcH' : ∀ i, c i ∈ H' := by
      intro i
      rcases hH'_cases (c i) (hRc i) with h | h
      · exact h
      · exfalso
        have hsub : ({b 0, b 1, b 2, c i} : Set W) ⊆ Set.range b ∪ Set.range c := by
          intro x hx
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          rcases hx with rfl | rfl | rfl | rfl <;> simp
        exact hne (closure_eq_top_of_subset_eq_top hsub h)
    have hsubset : Set.range a ∪ Set.range b ∪ Set.range c ⊆ (H' : Set W) := by
      intro x hx
      simp only [Set.mem_union, Set.mem_range] at hx
      rcases hx with (⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩
      · exact haH' i
      · exact hbH' i
      · exact hcH' i
    have hle : Subgroup.closure (Set.range a ∪ Set.range b ∪ Set.range c) ≤ H' :=
      (Subgroup.closure_le H').mpr hsubset
    rw [habc] at hle
    exact hH'_ne (eq_top_iff.mpr hle)
  exact ⟨hb12_eq, hc12_eq, hBC⟩

end CFSG.StandardType

end
