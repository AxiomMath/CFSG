module

public import CFSG.RankThree.PartTwo.Sec15.Item155wProofDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.RankThree.PartTwo.Sec15.Item155R2ProofCases

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def Step155GrowAltW (A : Subgroup G) (c : G) (L : Subgroup G) : Prop :=
  Sec14Std G A c L → ∀ X K Y M T : Subgroup G, Ctx155 A X K Y M T → MaxT155 A X K T →
    Above155w A X → ¬ K ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) →
    ⁅CFSG.Open.pCoreOf 2 K, K⁆ ≤ CFSG.Open.pCoreOf 2 Y →
    ¬ ⁅CFSG.Open.pCoreOf 2 Y, K⁆ ≤ CFSG.Open.pCoreOf 2 K →
    ((Case154Two L K X ∧
        ((¬ ∃ n : ℕ, 1 ≤ n ∧ Sec4.IsoLThreePi (↥X ⧸ CFSG.pCore 2 ↥X) 2 n) ∧
          IsEmpty (↥X ⧸ CFSG.pCore 2 ↥X ≃* alternatingGroup (Fin 5))) ∧
        ¬ ∃ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A ∧ L' ∈ lA A c' ∧
          L' = (L' ⊓ X) ⊔ CFSG.Open.pCoreOf 2 L') ∨
      (Case154Three A L K X (CFSG.Open.pCoreOf 2 Y) ∧
        ∃ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A ∧ L' ∈ lA A c' ∧
          L' = (L' ⊓ X) ⊔ CFSG.Open.pCoreOf 2 L')) →
      Claim155 A K Y

@[expose] noncomputable def Step155CasesNW (A : Subgroup G) (c : G) (L : Subgroup G) : Prop :=
  Sec14Std G A c L → ∀ X K Y M T : Subgroup G, Ctx155 A X K Y M T → MaxT155 A X K T →
    Above155w A X → ∀ J ∈ thetaComponentsIn M, J ∈ scriptY0 A (lB A) → X ≤ J →
      ∃ P : Subgroup G, Data155N A L X Y M T P J

@[expose] noncomputable def Step155RQKW (A : Subgroup G) (c : G) (L : Subgroup G) : Prop :=
  Sec14Std G A c L → ∀ X K Y M T P J : Subgroup G, Ctx155 A X K Y M T → MaxT155 A X K T →
    Above155w A X → J ∈ thetaComponentsIn M → J ∈ scriptY0 A (lB A) → X ≤ J →
    Data155N A L X Y M T P J →
      CFSG.Open.pCoreOf 2 (P ⊔ J) ⊓ n155 A K ≤ Subgroup.normalizer (K : Set G)

@[expose] noncomputable def Step155RQNW (A : Subgroup G) (c : G) (L : Subgroup G) : Prop :=
  Sec14Std G A c L → ∀ X K Y M T P J : Subgroup G, Ctx155 A X K Y M T → MaxT155 A X K T →
    Above155w A X → J ∈ thetaComponentsIn M → J ∈ scriptY0 A (lB A) → X ≤ J →
    Data155N A L X Y M T P J →
      CFSG.Open.pCoreOf 2 (P ⊔ J) ⊓ n155 A K ≤ CFSG.Open.pCoreOf 2 Y

@[expose] noncomputable def Step155GrowAltWR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step155GrowAltW A c L

@[expose] noncomputable def Step155CasesNWR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step155CasesNW A c L

end CFSG.RankThree.PartTwo.Sec15
