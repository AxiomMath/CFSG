module

public import CFSG.LocalAnalysis.StandardType.GGWitOrthClassR35Data

public section

namespace CFSG.StandardType.ZS.DataR35

theorem secondIso_of_check (w : Fin 5 → ZMod 3) (h : secondCheck w = true) :
    ∀ a : Fin 5 → ZMod 3, (∑ i, w i * (a i) ^ 2) = 1 →
    ∀ u : Fin 5 → ZMod 3, (∑ i, w i * (u i) ^ 2) = 0 →
      (2 * ∑ i, w i * (a i * u i)) = 0 → u ≠ 0 →
      ∃ u' : Fin 5 → ZMod 3, u' ≠ 0 ∧ (∑ i, w i * (u' i) ^ 2) = 0 ∧
        (2 * ∑ i, w i * (a i * u' i)) = 0 ∧
        (2 * ∑ i, w i * (u i * u' i)) = 0 ∧ u' ≠ u ∧ u' ≠ -u := by
  simp only [secondCheck, List.all_eq_true, List.any_eq_true, Bool.or_eq_true,
    Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_false', beq_iff_eq, beq_eq_false_iff_ne,
    bne_iff_ne, decide_eq_true_eq] at h
  intro a ha u hu huab hu0
  have hqa : qw w a = 1 := (qw_eq_iff w a 1).mpr ha
  have hqu : qw w u = 0 := (qw_eq_iff w u 0).mpr hu
  have hbu : bw w a u = 0 := (bw_eq_iff w a u 0).mpr huab
  rcases h a (mem_allV a) with h1 | h1
  · exact absurd hqa h1
  · rcases h1 u (mem_allV u) with h2 | h2
    · rcases h2 with h2 | h2
      · rcases h2 with h2 | h2
        · exact absurd hqu h2
        · exact absurd hbu h2
      · exact absurd h2 hu0
    · obtain ⟨u', hu'mem, hu'⟩ := h2
      rcases hu' with ⟨⟨⟨⟨⟨hu'ne, hu'q⟩, hu'a⟩, hu'u⟩, hu'neu⟩, hu'neneg⟩
      exact ⟨u', hu'ne, (qw_eq_iff w u' 0).mp hu'q, (bw_eq_iff w a u' 0).mp hu'a,
        (bw_eq_iff w u u' 0).mp hu'u, hu'neu, hu'neneg⟩

theorem secondIso_0 : ∀ a : Fin 5 → ZMod 3, (∑ i, wcan 0 i * (a i) ^ 2) = 1 →
    ∀ u : Fin 5 → ZMod 3, (∑ i, wcan 0 i * (u i) ^ 2) = 0 →
      (2 * ∑ i, wcan 0 i * (a i * u i)) = 0 → u ≠ 0 →
      ∃ u' : Fin 5 → ZMod 3, u' ≠ 0 ∧ (∑ i, wcan 0 i * (u' i) ^ 2) = 0 ∧
        (2 * ∑ i, wcan 0 i * (a i * u' i)) = 0 ∧
        (2 * ∑ i, wcan 0 i * (u i * u' i)) = 0 ∧ u' ≠ u ∧ u' ≠ -u :=
  secondIso_of_check (wcan 0) secondCheck_0

theorem secondIso_2 : ∀ a : Fin 5 → ZMod 3, (∑ i, wcan 2 i * (a i) ^ 2) = 1 →
    ∀ u : Fin 5 → ZMod 3, (∑ i, wcan 2 i * (u i) ^ 2) = 0 →
      (2 * ∑ i, wcan 2 i * (a i * u i)) = 0 → u ≠ 0 →
      ∃ u' : Fin 5 → ZMod 3, u' ≠ 0 ∧ (∑ i, wcan 2 i * (u' i) ^ 2) = 0 ∧
        (2 * ∑ i, wcan 2 i * (a i * u' i)) = 0 ∧
        (2 * ∑ i, wcan 2 i * (u i * u' i)) = 0 ∧ u' ≠ u ∧ u' ≠ -u :=
  secondIso_of_check (wcan 2) secondCheck_2

theorem secondIso_4 : ∀ a : Fin 5 → ZMod 3, (∑ i, wcan 4 i * (a i) ^ 2) = 1 →
    ∀ u : Fin 5 → ZMod 3, (∑ i, wcan 4 i * (u i) ^ 2) = 0 →
      (2 * ∑ i, wcan 4 i * (a i * u i)) = 0 → u ≠ 0 →
      ∃ u' : Fin 5 → ZMod 3, u' ≠ 0 ∧ (∑ i, wcan 4 i * (u' i) ^ 2) = 0 ∧
        (2 * ∑ i, wcan 4 i * (a i * u' i)) = 0 ∧
        (2 * ∑ i, wcan 4 i * (u i * u' i)) = 0 ∧ u' ≠ u ∧ u' ≠ -u :=
  secondIso_of_check (wcan 4) secondCheck_4

end CFSG.StandardType.ZS.DataR35

end
