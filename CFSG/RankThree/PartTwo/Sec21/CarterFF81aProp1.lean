module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartTwo.Sec21.FF81Defs

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

variable {G : Type} [Group G] [Finite G]

@[expose] def FF81aProp1RankStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (L : Subgroup G), FF81Hyp b L →
    localRank 3 G = 3 → (∀ g : G, g * b * g⁻¹ ∉ L) → KF_Sp6Torus →
      4 ≤ localRank 3 G

theorem kf_ff81aProp1_of_rankStep (hT : KF_Sp6Torus) (hStep : FF81aProp1RankStep) :
    KF_FF81aProp1 := by
  intro G _ _ b L h hrank
  by_contra hno
  push Not at hno
  have h4 := hStep G b L h hrank hno hT
  omega

end CFSG.RankThree.PartTwo.Sec21.FF81