module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3SmallRowsB6
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3SmallRowsB7

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem S16gRowCtx.false_of_alt_six_seven_L3 (h : S16gRowCtx D V₀ V L hV) (h3 : 3 ∈ D.sig)
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L) (barSub V₀ V hV D.T))
    (h7 : Nat.card ↥(irrSet (lBar V₀ V hV L)) = 7)
    (hL : UC22.IsAlt ↥(lBar V₀ V hV L) 6 ∨ UC22.IsAlt ↥(lBar V₀ V hV L) 7)
    (hK : Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) = 168) : False := by
  rcases hL with hL | hL
  · exact h.false_of_alt_six_L3 h3 hT h7 hL hK
  · exact h.false_of_alt_seven_L3 h3 hT h7 hL hK

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
