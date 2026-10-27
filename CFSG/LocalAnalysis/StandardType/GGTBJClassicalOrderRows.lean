module

public import CFSG.LocalAnalysis.StandardType.GGTBJLabelSides
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNineClassical

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem GGResHyp.not_classicalOrder
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hX : X = L ∨ X = K)
    (hMark : GGInnerDiagOnLabel GGTableBNbrInnerNineClassicalLabel p Bs X) : False := by
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hBound := not_largeEvenMarking_of_labelAll_card_lt (X := ↥X)
    (S := fun lab => GGTableBNbrInnerNineClassicalLabel p lab)
    (fun _ hΛ hcl => largeEvenLabelAll_card_lt_nineClassical Fact.out hp2 hΛ hcl)
  apply hBound
  rcases hX with rfl | rfl
  · exact ggInnerDiagOnLabel_L_pRank_ge_three hH.1 hMark
  · exact ggInnerDiagOnLabel_nbr_pRank_ge_three hH.1 hH.2.2.2.2.1 hMark

theorem ggTBJClassicalOrderLeft : GGTBJLeftOn GGTableBNbrInnerNineClassicalLabel := by
  intro G _ _ p B Bs x L D J y K hH _ hMark _
  exact (hH.not_classicalOrder (Or.inl rfl) hMark).elim

theorem ggTBJClassicalOrderNbr : GGTBJNbrOn GGTableBNbrInnerNineClassicalLabel := by
  intro G _ _ p B Bs x L D J y K hH _ hMark _
  exact (hH.not_classicalOrder (Or.inr rfl) hMark).elim

theorem ggTBJFieldTwoRestInput_of_order (h : GGTBJOrderRestInput) : GGTBJFieldTwoRestInput := by
  classical
  constructor
  · refine (h.1.or ggTBJClassicalOrderLeft).mono fun p lab hOld => ?_
    by_cases hcl : GGTableBNbrInnerNineClassicalLabel p lab
    · exact Or.inr hcl
    · exact Or.inl ⟨hOld, hcl⟩
  · refine (h.2.or ggTBJClassicalOrderNbr).mono fun p lab hOld => ?_
    by_cases hcl : GGTableBNbrInnerNineClassicalLabel p lab
    · exact Or.inr hcl
    · exact Or.inl ⟨hOld, hcl⟩

end CFSG.StandardType

end
