module

public import CFSG.Sporadic.Recognition.M23MultiplierTables

public section

namespace CFSG.Sporadic.Recognition.M23Multiplier

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Open CFSG.Sporadic.Recognition.CoverRecipe

theorem card_presentedGroup_le {c₂ c₁ : ℕ}
    (h₂ : subsetCheckCC m23Rels [0, 1, 2, 3, 4] c₂ 1288 = true)
    (h₁ : subsetCheckCC m23Rels5 [] c₁ 7920 = true) :
    Finite (PG 6 m23Rels) ∧ Nat.card (PG 6 m23Rels) ≤ 10200960 :=
  card_PG_le_chain h₂ h₁

theorem coverRelators_m23CommW : coverRelators (wordSet m23Rels) m23CommW = wordSet m23Cover :=
  coverRelators_wordSet m23Rels m23CommWord

theorem card_presentedCover_le {k c₄ c₃ : ℕ}
    (h₄ : subsetCheckShortCC m23Cover [0, 1, 2, 3, 4] k c₄ 1288 = true)
    (h₃ : subsetCheckShortCC m23Cover5 [] k c₃ 7920 = true) :
    Finite M23Cover ∧ Nat.card M23Cover ≤ 10200960 :=
  card_presentedCover_le_chain m23Rels m23CommWord h₄ h₃

theorem isPresentation_m23Gen (hTab : m23TabCheck = true)
    {c₂ c₁ : ℕ} (h₂ : subsetCheckCC m23Rels [0, 1, 2, 3, 4] c₂ 1288 = true)
    (h₁ : subsetCheckCC m23Rels5 [] c₁ 7920 = true) :
    IsPresentation m23Gen (wordSet m23Rels) :=
  isPresentation_of_chain (lift_m23Gen_rels hTab) (closure_m23Gen hTab) h₂ h₁
    (by rw [card_m23])

theorem lift_m23CommW (hTab : m23TabCheck = true) (i : Fin 6) :
    FreeGroup.lift m23Gen (m23CommW i) = m23Gen i :=
  lift_m23CommWord hTab i

theorem m23CommW_mem_commutator (i : Fin 6) : m23CommW i ∈ commutator (FreeGroup (Fin 6)) :=
  mk_commWords_mem_commutator _

section Multiplier


theorem card_griessHopfMultiplier_M23 (hTab : m23TabCheck = true)
    {c₂ c₁ c₄ c₃ k : ℕ} (h₂ : subsetCheckCC m23Rels [0, 1, 2, 3, 4] c₂ 1288 = true)
    (h₁ : subsetCheckCC m23Rels5 [] c₁ 7920 = true)
    (h₄ : subsetCheckShortCC m23Cover [0, 1, 2, 3, 4] k c₄ 1288 = true)
    (h₃ : subsetCheckShortCC m23Cover5 [] k c₃ 7920 = true) :
    Nat.card (griessHopfMultiplier CFSG.Blueprint.NativeSporadic.M23) = 1 :=
  card_griessHopfMultiplier_eq_one_of_chains (cw := m23CommWord) (lift_m23Gen_rels hTab)
    (closure_m23Gen hTab) (fun i => m23CommW_mem_commutator i) (fun i => lift_m23CommW hTab i)
    h₂ h₁ h₄ h₃ (by rw [card_m23]) (by rw [card_m23])

theorem card_ker_eq_one (hTab : m23TabCheck = true)
    {c₂ c₁ c₄ c₃ k : ℕ} (h₂ : subsetCheckCC m23Rels [0, 1, 2, 3, 4] c₂ 1288 = true)
    (h₁ : subsetCheckCC m23Rels5 [] c₁ 7920 = true)
    (h₄ : subsetCheckShortCC m23Cover [0, 1, 2, 3, 4] k c₄ 1288 = true)
    (h₃ : subsetCheckShortCC m23Cover5 [] k c₃ 7920 = true) {E : Type} [Group E]
    [Group.IsPerfect E] (q : E →* CFSG.Blueprint.NativeSporadic.M23) (hq : Function.Surjective q)
    (hker : q.ker ≤ Subgroup.center E) : Nat.card q.ker = 1 :=
  Nat.dvd_one.1 (card_ker_dvd_of_cover (p := 1) (cw := m23CommWord)
    (isPresentation_m23Gen hTab h₂ h₁)
    (fun i => m23CommW_mem_commutator i) (fun i => lift_m23CommW hTab i)
    (card_griessHopfMultiplier_M23 hTab h₂ h₁ h₄ h₃) q hq hker)

theorem card_center_eq_one (hTab : m23TabCheck = true)
    {c₂ c₁ c₄ c₃ k : ℕ} (h₂ : subsetCheckCC m23Rels [0, 1, 2, 3, 4] c₂ 1288 = true)
    (h₁ : subsetCheckCC m23Rels5 [] c₁ 7920 = true)
    (h₄ : subsetCheckShortCC m23Cover [0, 1, 2, 3, 4] k c₄ 1288 = true)
    (h₃ : subsetCheckShortCC m23Cover5 [] k c₃ 7920 = true) {Q : Type} [Group Q]
    (hQ : Group.IsPerfect Q)
    (e : Q ⧸ Subgroup.center Q ≃* CFSG.Blueprint.NativeSporadic.M23) :
    Nat.card (Subgroup.center Q) = 1 :=
  Nat.dvd_one.1 (card_center_dvd_of_cover (p := 1) (cw := m23CommWord)
    (isPresentation_m23Gen hTab h₂ h₁)
    (fun i => m23CommW_mem_commutator i) (fun i => lift_m23CommW hTab i)
    (card_griessHopfMultiplier_M23 hTab h₂ h₁ h₄ h₃) hQ e)

end Multiplier

end CFSG.Sporadic.Recognition.M23Multiplier
