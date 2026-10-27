module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.BarOutInner
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec3.TwoThreeStructure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.LocalAnalysis.UniquenessCase.UC22

theorem inner_action_of_not_three_dvd_outer
    {G : Type} [Group G] [Finite G] {L P : Subgroup G}
    (hOut : ¬ 3 ∣ Nat.card
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer (Bar2 L)))
    (hP3 : IsPGroup 3 P)
    (hPNL : P ≤ Subgroup.normalizer (L : Set G)) :
    ∀ x ∈ P, ∃ l ∈ L, ∀ y ∈ L,
      (x * y * x⁻¹) * (l * y * l⁻¹)⁻¹ ∈ CFSG.Open.pCoreOf 2 L := by
  intro x hx
  exact exists_conj_of_not_three_dvd_outer x (hPNL hx)
    (hP3.to_le (Subgroup.zpowers_le.mpr hx)) hOut

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
