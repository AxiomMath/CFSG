module

public import CFSG.Sporadic.Recognition.HSMultiplierTables

public section

namespace CFSG.Sporadic.Recognition.HSMultiplier

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Open CFSG.Sporadic.Recognition.CoverRecipe
  CFSG.Sporadic.SmallF2
open CFSG.Sporadic.HS.Native (hsData)

theorem card_presentedGroup_le {c₂ c₁ : ℕ}
    (h₂ : subsetCheckCC hsRels [0, 1, 2, 3, 4] c₂ 5600 = true)
    (h₁ : subsetCheckCC hsRels5 [] c₁ 7920 = true) :
    Finite (PG 6 hsRels) ∧ Nat.card (PG 6 hsRels) ≤ 44352000 :=
  card_PG_le_chain h₂ h₁

theorem coverRelators_hsCommW : coverRelators (wordSet hsRels) hsCommW = wordSet hsCover :=
  coverRelators_wordSet hsRels hsCommWord

theorem card_presentedCover_le {k c₄ c₃ : ℕ}
    (h₄ : subsetCheckShortCC hsCover [0, 1, 2, 3, 4] k c₄ 11200 = true)
    (h₃ : subsetCheckShortCC hsCover5 [] k c₃ 7920 = true) :
    Finite HSCover ∧ Nat.card HSCover ≤ 88704000 :=
  card_presentedCover_le_chain hsRels hsCommWord h₄ h₃

theorem isPresentation_hsGen (hTab : hsTabCheck = true)
    {c₂ c₁ : ℕ} (h₂ : subsetCheckCC hsRels [0, 1, 2, 3, 4] c₂ 5600 = true)
    (h₁ : subsetCheckCC hsRels5 [] c₁ 7920 = true) :
    IsPresentation hsGen (wordSet hsRels) := by
  obtain ⟨hfin, hle⟩ := card_presentedGroup_le h₂ h₁
  have : Finite (PresentedGroup (wordSet hsRels)) := hfin
  exact IsPresentation.of_card_le (lift_hsGen_rels hTab) (closure_hsGen hTab) (by
    rw [card_J]; exact hle)

theorem lift_hsCommW (hTab : hsTabCheck = true) (i : Fin 6) :
    FreeGroup.lift hsGen (hsCommW i) = hsGen i :=
  lift_hsCommWord hTab i

theorem hsCommW_mem_commutator (i : Fin 6) : hsCommW i ∈ commutator (FreeGroup (Fin 6)) :=
  mk_commWords_mem_commutator _

section Multiplier


theorem card_griessHopfMultiplier_J_le (hTab : hsTabCheck = true)
    {c₂ c₁ c₄ c₃ k : ℕ} (h₂ : subsetCheckCC hsRels [0, 1, 2, 3, 4] c₂ 5600 = true)
    (h₁ : subsetCheckCC hsRels5 [] c₁ 7920 = true)
    (h₄ : subsetCheckShortCC hsCover [0, 1, 2, 3, 4] k c₄ 11200 = true)
    (h₃ : subsetCheckShortCC hsCover5 [] k c₃ 7920 = true) :
    0 < Nat.card (griessHopfMultiplier (J hsData)) ∧
      Nat.card (griessHopfMultiplier (J hsData)) ≤ 2 :=
  card_griessHopfMultiplier_le_of_cover (p := 2) (cw := hsCommWord)
    (isPresentation_hsGen hTab h₂ h₁) (fun i => hsCommW_mem_commutator i)
    (fun i => lift_hsCommW hTab i) (by
      rw [card_J]
      exact card_presentedCover_le h₄ h₃)

theorem card_center_le_two (hTab : hsTabCheck = true)
    {c₂ c₁ c₄ c₃ k : ℕ} (h₂ : subsetCheckCC hsRels [0, 1, 2, 3, 4] c₂ 5600 = true)
    (h₁ : subsetCheckCC hsRels5 [] c₁ 7920 = true)
    (h₄ : subsetCheckShortCC hsCover [0, 1, 2, 3, 4] k c₄ 11200 = true)
    (h₃ : subsetCheckShortCC hsCover5 [] k c₃ 7920 = true) {Q : Type} [Group Q]
    (hQ : Group.IsPerfect Q)
    (e : Q ⧸ Subgroup.center Q ≃* CFSG.Blueprint.NativeSporadic.HS) :
    Nat.card (Subgroup.center Q) ≤ 2 := by
  obtain ⟨hpos, hle⟩ := card_griessHopfMultiplier_J_le hTab h₂ h₁ h₄ h₃
  have hd := card_center_dvd_of_cover (p := Nat.card (griessHopfMultiplier (J hsData)))
    (cw := hsCommWord) (isPresentation_hsGen hTab h₂ h₁) (fun i => hsCommW_mem_commutator i)
    (fun i => lift_hsCommW hTab i) rfl hQ (e.trans CFSG.Sporadic.Bridge.HS.nativeEquiv)
  exact (Nat.le_of_dvd hpos hd).trans hle

end Multiplier

end CFSG.Sporadic.Recognition.HSMultiplier
