module

public import CFSG.LocalAnalysis.UniqueFourCatalog.SmallExceptional
public import CFSG.LocalAnalysis.UniqueFourCatalog.ExceptionalTwo
public import CFSG.LocalAnalysis.UniqueFourCatalog.ExceptionalTwoTwisted
public import CFSG.LocalAnalysis.UniqueFourCatalog.OddExceptionalEasy
public import CFSG.LocalAnalysis.UniqueFourCatalog.TwistedOddInputs

open CFSG.Open
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4)

public section

namespace CFSG.LocalAnalysis.UniqueFourCatalog

open CFSG.Blueprint CFSG.Assembly.LowTwoRank

set_option linter.unusedSectionVars false


variable {G : Type} [Group G] [Finite G]

theorem false_of_chevalleyExceptional_odd (h₁ : TwistedE6OddExclusion) (h₂ : TrialityD4OddExclusion)
    (h₃ : UntwistedExceptionalOddExclusion) (hS : Standing4 G) {t : StatedLieTag} {p f : ℕ}
    (ht : t ∈ chevalleyExceptionalTags) (hp : p ≠ 2) (h : ChevalleyExceptionalModel G t p f) :
    False := by
  simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact false_of_G2_odd hS hp h
  · exact h₃ G hS _ (Or.inl rfl) p f hp h
  · exact h₃ G hS _ (Or.inr (Or.inl rfl)) p f hp h
  · exact h₃ G hS _ (Or.inr (Or.inr (Or.inl rfl))) p f hp h
  · exact h₃ G hS _ (Or.inr (Or.inr (Or.inr rfl))) p f hp h
  · exact h₁ G hS p f hp h
  · exact h₂ G hS p f hp h

theorem not_uniqueFour_of_chevalleyExceptional_two (hS : Standing4 G) {t : StatedLieTag}
    {f : ℕ} (ht : t ∈ chevalleyExceptionalTags) (h : ChevalleyExceptionalModel G t 2 f) :
    ¬ uniqueFourUnique G := by
  simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun _ => Standing4.false_of_smallExceptionalTwoCase hS (Or.inr (Or.inl ⟨f, h⟩))
  · exact not_uniqueFour_of_untwistedChevalleyModel_two .F4 hS (by simpa using h.2)
  · exact not_uniqueFour_of_untwistedChevalleyModel_two .E6 hS (by simpa using h.2)
  · exact not_uniqueFour_of_untwistedChevalleyModel_two .E7 hS (by simpa using h.2)
  · exact not_uniqueFour_of_untwistedChevalleyModel_two .E8 hS (by simpa using h.2)
  · exact not_uniqueFour_of_twistedChevalleyModel_two hS .E6 (by simpa using h.2)
  · exact fun _ => Standing4.false_of_smallExceptionalTwoCase hS
      (Or.inr (Or.inr (Or.inl ⟨f, h⟩)))

theorem false_of_reeTits (hS : Standing4 G) {t : StatedLieTag} {p f : ℕ} (ht : t ∈ reeTitsTags)
    (h : ReeTitsModel G t p f) : False := by
  simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl
  · exact false_of_reeG2 hS h
  · obtain rfl : p = 2 := h.1.2.2.2.1
    exact Standing4.false_of_smallExceptionalTwoCase hS (Or.inr (Or.inr (Or.inr (Or.inl ⟨f, h⟩))))
  · obtain rfl : p = 2 := h.1.2.2.2.1
    exact Standing4.false_of_smallExceptionalTwoCase hS (Or.inr (Or.inr (Or.inr (Or.inr ⟨f, h⟩))))

theorem false_of_suzuki (hS : Standing4 G) {p f : ℕ} (h : SuzukiModel G p f) : False := by
  obtain rfl : p = 2 := h.1
  exact Standing4.false_of_smallExceptionalTwoCase hS (Or.inl ⟨f, h⟩)

theorem not_uniqueFour_of_exceptionalRep (h₁ : TwistedE6OddExclusion)
    (h₂ : TrialityD4OddExclusion) (h₃ : UntwistedExceptionalOddExclusion) (hS : Standing4 G)
    (h : ExceptionalRep G) : ¬ uniqueFourUnique G := by
  rcases h with ⟨t, p, f, ht, hm⟩ | ⟨t, p, f, ht, hm⟩ | ⟨p, f, hm⟩
  · by_cases hp : p = 2
    · subst hp
      exact not_uniqueFour_of_chevalleyExceptional_two hS ht hm
    · exact fun _ => false_of_chevalleyExceptional_odd h₁ h₂ h₃ hS ht hp hm
  · exact fun _ => false_of_reeTits hS ht hm
  · exact fun _ => false_of_suzuki hS hm

end CFSG.LocalAnalysis.UniqueFourCatalog
