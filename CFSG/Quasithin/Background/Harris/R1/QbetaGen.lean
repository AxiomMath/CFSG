module

import Mathlib.Tactic.IntervalCases
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.Coset.Card

public section

namespace CFSG.Quasithin.Background.Harris.R1

variable {G : Type*} [Group G] [Finite G]

theorem exists_two_gen {V A : Subgroup G} (hVA : V ≤ A) (hV : Nat.card V = 4)
    (hA : Nat.card A = 16) :
    ∃ a1 ∈ A, ∃ a2 ∈ A, A ≤ Subgroup.closure ((V : Set G) ∪ {a1, a2}) := by
  classical
  have hVA' : ∃ a1 ∈ A, a1 ∉ V := by
    by_contra hcon
    push Not at hcon
    have hle : A ≤ V := hcon
    have := Subgroup.card_le_of_le hle
    omega
  obtain ⟨a1, ha1, ha1V⟩ := hVA'
  set B1 := Subgroup.closure ((V : Set G) ∪ {a1}) with hB1
  have hB1A : B1 ≤ A := by
    rw [hB1, Subgroup.closure_le]
    rintro x (hx | hx)
    · exact hVA hx
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]; exact ha1
  have hVB1 : V ≤ B1 := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have ha1B1 : a1 ∈ B1 := Subgroup.subset_closure (Or.inr rfl)
  have hB1card : 4 < Nat.card B1 := by
    have h1 := Subgroup.card_le_of_le hVB1
    rcases Nat.lt_or_ge 4 (Nat.card B1) with h | h
    · exact h
    · exfalso
      have heq : V = B1 := Subgroup.eq_of_le_of_card_ge hVB1 (by omega)
      exact ha1V (heq ▸ ha1B1)
  have hB1d : Nat.card B1 ∣ 16 := hA ▸ Subgroup.card_dvd_of_le hB1A
  by_cases h16 : Nat.card B1 = 16
  · refine ⟨a1, ha1, a1, ha1, ?_⟩
    have hAB1 : B1 = A := Subgroup.eq_of_le_of_card_ge hB1A (by omega)
    intro x hx
    rw [← hAB1] at hx
    have : Subgroup.closure ((V : Set G) ∪ {a1}) ≤ Subgroup.closure ((V : Set G) ∪ {a1, a1}) := by
      apply Subgroup.closure_mono
      intro y hy
      rcases hy with hy | hy
      · exact Or.inl hy
      · exact Or.inr (Or.inl hy)
    exact this hx
  · have h8 : Nat.card B1 = 8 := by
      have hle : Nat.card B1 ≤ 16 := Nat.le_of_dvd (by norm_num) hB1d
      generalize Nat.card B1 = c at hB1card hB1d h16 hle ⊢
      interval_cases c <;> omega
    have hex : ∃ a2 ∈ A, a2 ∉ B1 := by
      by_contra hcon
      push Not at hcon
      have hle : A ≤ B1 := hcon
      have := Subgroup.card_le_of_le hle
      omega
    obtain ⟨a2, ha2, ha2B1⟩ := hex
    refine ⟨a1, ha1, a2, ha2, ?_⟩
    set B2 := Subgroup.closure ((V : Set G) ∪ {a1, a2}) with hB2
    have hB2A : B2 ≤ A := by
      rw [hB2, Subgroup.closure_le]
      rintro x (hx | hx)
      · exact hVA hx
      · rcases hx with hx | hx
        · rw [hx]; exact ha1
        · rw [Set.mem_singleton_iff.mp hx]; exact ha2
    have hB1B2 : B1 ≤ B2 := by
      apply Subgroup.closure_mono
      intro y hy
      rcases hy with hy | hy
      · exact Or.inl hy
      · exact Or.inr (Or.inl hy)
    have ha2B2 : a2 ∈ B2 := Subgroup.subset_closure (Or.inr (Or.inr rfl))
    have hB2card : 8 < Nat.card B2 := by
      have h1 := Subgroup.card_le_of_le hB1B2
      rcases Nat.lt_or_ge 8 (Nat.card B2) with h | h
      · exact h
      · exfalso
        have heq : B1 = B2 := Subgroup.eq_of_le_of_card_ge hB1B2 (by omega)
        exact ha2B1 (heq ▸ ha2B2)
    have hB2d : Nat.card B2 ∣ 16 := hA ▸ Subgroup.card_dvd_of_le hB2A
    have hB2le : Nat.card B2 ≤ 16 := Nat.le_of_dvd (by norm_num) hB2d
    have h16' : Nat.card B2 = 16 := by
      generalize Nat.card B2 = c at hB2card hB2d hB2le
      interval_cases c <;> omega
    have : B2 = A := Subgroup.eq_of_le_of_card_ge hB2A (by omega)
    exact this.ge

end CFSG.Quasithin.Background.Harris.R1
