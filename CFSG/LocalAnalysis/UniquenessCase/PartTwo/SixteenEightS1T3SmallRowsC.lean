module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8RowBase
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3OutThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3OutTab

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem S16gRowCtx.false_of_card_irr_three_special (h : S16gRowCtx D V₀ V L hV)
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L) (barSub V₀ V hV D.T))
    (h3' : Nat.card ↥(irrSet (lBar V₀ V hV L)) = 3)
    (hL : IsSLn ↥(lBar V₀ V hV L) 3 1 ∨ IsSLn ↥(lBar V₀ V hV L) 4 1 ∨
      IsOmegaMinus ↥(lBar V₀ V hV L) 4 1 ∨ IsOmegaMinus ↥(lBar V₀ V hV L) 6 1 ∨
      UC22.IsAlt ↥(lBar V₀ V hV L) 5 ∨ UC22.IsAlt ↥(lBar V₀ V hV L) 6 ∨
      UC22.IsAlt ↥(lBar V₀ V hV L) 7) : False := by
  haveI : Finite (MulAut (Vtil V₀ V hV)) := MulEquiv.finite_left
  haveI : Finite ↥(lBar V₀ V hV L) := Subtype.finite
  refine s16t3_not_three_dvd_outer h.quasi ?_ (hT.three_dvd_card_outer h3')
  rcases hL with hL | hL | hL | hL | hL | hL | hL
  · exact ⟨3, Or.inl ⟨hL, by norm_num⟩⟩
  · exact ⟨4, Or.inl ⟨hL, by norm_num⟩⟩
  · exact ⟨4, Or.inr (Or.inr (Or.inr (Or.inl ⟨hL, by norm_num⟩)))⟩
  · exact ⟨6, Or.inr (Or.inr (Or.inr (Or.inl ⟨hL, by norm_num⟩)))⟩
  · exact ⟨5, Or.inr (Or.inr (Or.inr (Or.inr ⟨hL, by norm_num⟩)))⟩
  · exact ⟨6, Or.inr (Or.inr (Or.inr (Or.inr ⟨hL, by norm_num⟩)))⟩
  · exact ⟨7, Or.inr (Or.inr (Or.inr (Or.inr ⟨hL, by norm_num⟩)))⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
