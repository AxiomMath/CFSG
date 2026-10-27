module

public import CFSG.RankThree.PartTwo.Sec17.RouteForms
public import CFSG.RankThree.PartTwo.Sec14.Concl142HJ
import CFSG.RankThree.PartTwo.Sec14.Item148Solvable
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec17

@[expose] noncomputable def Concl142NHJS14 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ¬ AllPointsHJ A → Concl142 A (lB A)

@[expose] noncomputable def Concl142R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Concl142 A (lB A)

@[expose] noncomputable def Item146R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Item146 A (lB A)

theorem concl142S14_of_nhj
    (h : Concl142NHJS14) : Concl142S14 := by
  intro G _ _ A c L hs
  by_cases hHJ : AllPointsHJ A
  · exact concl142_of_allPointsHJ hs hHJ
  · exact h G A c L hs hHJ

theorem concl142R_of_S14 (h : Concl142S14) : Concl142R :=
  fun G _ _ A c L hR => h G A c L hR.toSec14Std

theorem item146R_of_S14 (h : Item146S14) : Item146R :=
  fun G _ _ A c L hR => h G A c L hR.toSec14Std

theorem claim1411LocalR_of' (h146 : Item146R) (hbot : Item145BotS14)
    (hW : Claim1411NonsolvWR) (hX : Claim1411NonsolvXR) : Claim1411LocalR :=
  fun G _ _ A c L hR => claim1411Local_of_nonsolvable hR.toSec14Std (h146 G A c L hR)
    (hbot G A c L hR.toSec14Std) (hW G A c L hR) (hX G A c L hR)

end CFSG.RankThree.PartTwo.Sec14
