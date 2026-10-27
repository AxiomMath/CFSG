module

public import CFSG.LocalAnalysis.StandardType.GGTBJOrthLeft
public import CFSG.LocalAnalysis.StandardType.GGTBJOrthNbr
public import CFSG.LocalAnalysis.StandardType.GGTBJFamilyStages

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggTBJOrthLabel.cases {p : ℕ} {lab : LargeEvenLabel} (h : ggTBJOrthLabel p lab) :
    (1 ≤ lab.n ∧ GGTBRowR5O1 p lab) ∨ (1 ≤ lab.n ∧ GGTBRowR5O2 p lab) ∨
      (1 ≤ lab.n ∧ lab.tag = .D ∧ 4 ≤ lab.rank ∧ p ∣ 2 ^ lab.n - 1) ∨
      (1 ≤ lab.n ∧ lab.tag = .D ∧ 4 ≤ lab.rank ∧ Even lab.rank ∧ p ∣ 2 ^ lab.n + 1) ∨
      (1 ≤ lab.n ∧ lab.tag = .D ∧ 4 ≤ lab.rank ∧ Odd lab.rank ∧ p ∣ 2 ^ lab.n + 1) := by
  obtain ⟨hq, htag, h4, hp⟩ := h
  rcases htag with htag | htag
  · rcases hp with hp | hp
    · exact Or.inr (Or.inr (Or.inl ⟨hq, htag, h4, hp⟩))
    · rcases Nat.even_or_odd lab.rank with he | ho
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hq, htag, h4, he, hp⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hq, htag, h4, ho, hp⟩)))
  · rcases hp with hp | hp
    · exact Or.inl ⟨hq, htag, h4, Or.inl hp⟩
    · rcases Nat.even_or_odd lab.rank with he | ho
      · exact Or.inl ⟨hq, htag, h4, Or.inr ⟨he, hp⟩⟩
      · exact Or.inr (Or.inl ⟨hq, htag, h4, ho, hp⟩)

theorem ggTBJLeftOn_orth :
    GGTBJLeftOn ggTBJOrthLabel := by
  have hrow : ∀ {S : ℕ → LargeEvenLabel → Prop},
      (∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (B Bs : Subgroup G) (x : G)
        (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K →
          GGInnerDiagOnLabel S p Bs L → GGResSideDatum p Bs L J ∨ GGResLeviSideDatumLE3 p Bs L J) →
      GGTBJLeftOn S := by
    intro S h G _ _ p B Bs x L D J y K hH hp hL _hX
    rcases h G p B Bs x L D J y K hH hL with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  have h1 := hrow (S := fun p lab => 1 ≤ lab.n ∧ GGTBRowR5O1 p lab)
    fun G _ _ p _ B Bs x L D J y K hH hL => ggTBJOrthLeft_rowR5O1 hH hL
  have h2 := hrow (S := fun p lab => 1 ≤ lab.n ∧ GGTBRowR5O2 p lab)
    fun G _ _ p _ B Bs x L D J y K hH hL => ggTBJOrthLeft_rowR5O2 hH hL
  have h3 := hrow (S := fun p lab => 1 ≤ lab.n ∧ lab.tag = .D ∧ 4 ≤ lab.rank ∧
      p ∣ 2 ^ lab.n - 1)
    fun G _ _ p _ B Bs x L D J y K hH hL => ggTBJOrthLeft_rowOmPlusMinus hH hL
  have h4 := hrow (S := fun p lab => 1 ≤ lab.n ∧ lab.tag = .D ∧ 4 ≤ lab.rank ∧
      Even lab.rank ∧ p ∣ 2 ^ lab.n + 1)
    fun G _ _ p _ B Bs x L D J y K hH hL => ggTBJOrthLeft_rowOmPlusPlusEven hH hL
  have h5 := hrow (S := fun p lab => 1 ≤ lab.n ∧ lab.tag = .D ∧ 4 ≤ lab.rank ∧
      Odd lab.rank ∧ p ∣ 2 ^ lab.n + 1)
    fun G _ _ p _ B Bs x L D J y K hH hL => ggTBJOrthLeft_rowOmPlusPlusOdd hH hL
  exact (h1.or (h2.or (h3.or (h4.or h5)))).mono fun p lab hl => ggTBJOrthLabel.cases hl

theorem ggTBJNbrOn_orth
    (hI3 : GGNbrSubcomponentInput) :
    GGTBJNbrOn ggTBJOrthLabel := by
  have hrow : ∀ {S : ℕ → LargeEvenLabel → Prop},
      (∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (B Bs : Subgroup G) (x : G)
        (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K →
          GGInnerDiagOnLabel S p Bs K → GGResSideDatum p Bs K J ∨ GGResLeviSideDatumLE3 p Bs K J) →
      GGTBJNbrOn S := by
    intro S h G _ _ p B Bs x L D J y K hH hp hK _hX
    rcases h G p B Bs x L D J y K hH hK with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  have h1 := hrow (S := fun p lab => 1 ≤ lab.n ∧ GGTBRowR5O1 p lab)
    fun G _ _ p _ B Bs x L D J y K hH hK => ggTBJOrthNbr_rowR5O1 hI3 hH hK
  have h2 := hrow (S := fun p lab => 1 ≤ lab.n ∧ GGTBRowR5O2 p lab)
    fun G _ _ p _ B Bs x L D J y K hH hK => ggTBJOrthNbr_rowR5O2 hI3 hH hK
  have h3 := hrow (S := fun p lab => 1 ≤ lab.n ∧ lab.tag = .D ∧ 4 ≤ lab.rank ∧
      p ∣ 2 ^ lab.n - 1)
    fun G _ _ p _ B Bs x L D J y K hH hK => ggTBJOrthNbr_rowOmPlusMinus hI3 hH hK
  have h4 := hrow (S := fun p lab => 1 ≤ lab.n ∧ lab.tag = .D ∧ 4 ≤ lab.rank ∧
      Even lab.rank ∧ p ∣ 2 ^ lab.n + 1)
    fun G _ _ p _ B Bs x L D J y K hH hK => ggTBJOrthNbr_rowOmPlusPlusEven hI3 hH hK
  have h5 := hrow (S := fun p lab => 1 ≤ lab.n ∧ lab.tag = .D ∧ 4 ≤ lab.rank ∧
      Odd lab.rank ∧ p ∣ 2 ^ lab.n + 1)
    fun G _ _ p _ B Bs x L D J y K hH hK => ggTBJOrthNbr_rowOmPlusPlusOdd hI3 hH hK
  exact (h1.or (h2.or (h3.or (h4.or h5)))).mono fun p lab hl => ggTBJOrthLabel.cases hl

end CFSG.StandardType

end
