module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

@[expose] def R16_3FComp (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Setting16 D V₀ V L →
    Conc4_136 D V₀ V hV L → 1 < s15 D.M V₀ V hV L →
    IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV) →
    (∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ 2 ≤ CFSG.Open.pRank q (lBar V₀ V hV L)) →
    Concl163F D V₀ V hV L

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
