module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7DSmallDefs
import CFSG.LocalAnalysis.StandardType.GGHdRo7DSmallBasic

public section

namespace CFSG.StandardType.HdRo7D.Small

open CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma hdRo7DSmTargetAux_rho_eq_one_or_two {ρ : ZMod 3} (hρ : ρ ≠ 0) :
    ρ = 1 ∨ ρ = 2 := by
  have h : ρ = 0 ∨ ρ = 1 ∨ ρ = 2 := by
    have hall : ∀ x : ZMod 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
    exact hall ρ
  rcases h with h | h | h
  · exact absurd h hρ
  · exact Or.inl h
  · exact Or.inr h

theorem dSmTarget_of_leaves : DNormalizerLeaf → DReflFixLeaf → (DNormalizerLeaf → DReflFixLeaf → ∀
    (n : ℕ) (H A : Subgroup (DGL n)), DLinData 3 n (DV n) (dStd n) H A → (∃ r ∈ H, GGLinRefl r ∧ ¬
    ggLinMove r ≤ LinearMap.ker ((dStd n).coord 0)) → ∃ ρ : ZMod 3, ρ ≠ 0 ∧ (∀ r ∈ H, GGLinRefl r →
    ∃ h, DRefl ρ r h) ∧ DRCl ρ (dRoots ρ H)) → DSmTransLeaf →
    DSmClassLeaf → DSmModelsBDLeaf → DSmGenLeaf → DSmModelsE7Leaf → DSmModelsE8Leaf →
    (∀ (n : ℕ), (n = 6 ∨ n = 7) → ∀ (H A : Subgroup (DGL n)), DLinData 3 n (DV n) (dStd n) H A → (∃
        r ∈ H, GGLinRefl r ∧ ¬ ggLinMove r ≤ LinearMap.ker ((dStd n).coord 0)) → ZS.LinWeyl 3
        H) := by
  intro hN hF hRules hTrans hClass hBD hGen hE7 hE8 n hn H A hD hext
  obtain ⟨ρ, hρ, hrefl, hRCl⟩ := hRules hN hF n H A hD hext
  have hHG : H = dGroup ρ (dRoots ρ H) := by
    apply le_antisymm
    · obtain ⟨S, hS, hHcl, _⟩ := hD.hgen
      rw [hHcl]
      rw [Subgroup.closure_le]
      intro s hs
      obtain ⟨hsH, hsRefl⟩ := hS s hs
      obtain ⟨h, hh⟩ := hrefl s hsH hsRefl
      exact Subgroup.subset_closure ⟨h, ⟨s, hHcl ▸ hsH, hh⟩, hh⟩
    · rw [dGroup, Subgroup.closure_le]
      rintro r ⟨h, ⟨r', hr'H, hr'⟩, hr⟩
      rw [dRefl_unique hr hr']
      exact hr'H
  have hCl := hClass hTrans
  rcases hn with rfl | rfl
  · obtain rfl | rfl : ρ = 1 ∨ ρ = 2 := hdRo7DSmTargetAux_rho_eq_one_or_two hρ
    · rw [hHG]
      rcases hCl.1 (dRoots 1 H) hRCl with hΦ | hΦ
      · rw [hΦ]
        exact hBD.1
      · rw [hΦ]
        exact hBD.2.1
    · rw [hHG]
      rcases hCl.2.1 (dRoots 2 H) hRCl with hΦ | hΦ
      · rw [hΦ]
        exact (hE7 hGen hTrans).1
      · rw [hΦ]
        exact (hE7 hGen hTrans).2
  · obtain rfl | rfl : ρ = 1 ∨ ρ = 2 := hdRo7DSmTargetAux_rho_eq_one_or_two hρ
    · rw [hHG]
      rcases hCl.2.2.1 (dRoots 1 H) hRCl with hΦ | hΦ | hΦ | hΦ
      · rw [hΦ]
        exact hBD.2.2.1
      · rw [hΦ]
        exact hBD.2.2.2
      · rw [hΦ]
        exact (hE8 hGen hTrans).1
      · rw [hΦ]
        exact (hE8 hGen hTrans).2
    · exact absurd hRCl (hCl.2.2.2 (dRoots 2 H))

end CFSG.StandardType.HdRo7D.Small
