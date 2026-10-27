module

public import CFSG.RankThree.PartTwo.Sec17.RouteWire15
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

@[expose] noncomputable def Claim153TwinTypes : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y ∈ scriptY0Star A (lB A), ¬ HasFaithfulE9 Y →
      ∀ M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G),
        ¬ M ≤ Subgroup.normalizer (Y : Set G) →
          Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 5)) ∨
            Sec4.IsTripleCover (↥Y ⧸ CFSG.pCore 2 ↥Y) (alternatingGroup (Fin 6))

@[expose] noncomputable def Claim153NoTwinA5A6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y ∈ scriptY0Star A (lB A), ¬ HasFaithfulE9 Y →
      (Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 5)) ∨
        Sec4.IsTripleCover (↥Y ⧸ CFSG.pCore 2 ↥Y) (alternatingGroup (Fin 6))) →
      ∀ M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G),
        M ≤ Subgroup.normalizer (Y : Set G)

theorem claim153NormalNoE9R_of (htypes : Claim153TwinTypes) (hno : Claim153NoTwinA5A6) :
    Claim153NormalNoE9R := by
  intro G _ _ A c L hR Y hY hE M hM
  by_contra hMY
  exact hMY (hno G A c L hR Y hY hE (htypes G A c L hR Y hY hE M hM hMY) M hM)

end CFSG.RankThree.PartTwo.Sec15
