module

public import CFSG.RankThree.PartTwo.Sec15.Ronan152SixBigDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.RankThree.PartTwo.Sec14.Concl142HJ
public import CFSG.RankThree.PartTwo.Sec15.Item155R2ProofCases
public import CFSG.RankThree.PartTwo.Sec15.Item155wProofDefs

public section

namespace CFSG.RankThree.PartTwo.Sec15.Ronan155Big

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def Item155wBig (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y ∈ scriptY3 A LB, oPrimeResidualOf 3 Y ∈ scriptY4 A LB → Big152 (oPrimeResidualOf 3 Y) →
    Y = oPrimeResidualOf 3 Y ⊔ CFSG.Open.pCoreOf 2 Y →
      (omg155 A (oPrimeResidualOf 3 Y) → (gam155 A LB Y (oPrimeResidualOf 3 Y)).Nonempty) ∧
      ∀ K ∈ gam155 A LB Y (oPrimeResidualOf 3 Y),
        (omg155 A (oPrimeResidualOf 3 Y) ∨
          K = oPrimeResidualOf 3 Y ⊔ CFSG.Open.pCoreOf 2 K) →
        ∀ M ∈ CFSG.maximalTwoLocalsContaining ((A ⊔ Y : Subgroup G) : Set G),
          delta A LB M ≤ Subgroup.normalizer
            (oPrimeResidualOf 3 (delta A LB (Subgroup.normalizer (K : Set G))) : Set G)

theorem item155wBig_iff {A : Subgroup G} :
    Item155wBig A (lB A) ↔
      ∀ Y, IsY155 A Y → Big152 (oPrimeResidualOf 3 Y) → One155 A Y ∧ Two155w A Y :=
  ⟨fun h Y hY hb => h Y hY.1 hY.2.1 hb hY.2.2, fun h Y hY hX hb hYX => h Y ⟨hY, hX, hYX⟩ hb⟩

@[expose] noncomputable def Step155RQKWBig (A : Subgroup G) (c : G) (L : Subgroup G) : Prop :=
  Sec14Std G A c L → ∀ X K Y M T P J : Subgroup G, Ctx155 A X K Y M T → Big152 X →
    MaxT155 A X K T → Above155w A X → J ∈ thetaComponentsIn M → J ∈ scriptY0 A (lB A) → X ≤ J →
    Data155N A L X Y M T P J →
      CFSG.Open.pCoreOf 2 (P ⊔ J) ⊓ n155 A K ≤ Subgroup.normalizer (K : Set G)

@[expose] noncomputable def Step155RQNWBig (A : Subgroup G) (c : G) (L : Subgroup G) : Prop :=
  Sec14Std G A c L → ∀ X K Y M T P J : Subgroup G, Ctx155 A X K Y M T → Big152 X →
    MaxT155 A X K T → Above155w A X → J ∈ thetaComponentsIn M → J ∈ scriptY0 A (lB A) → X ≤ J →
    Data155N A L X Y M T P J →
      CFSG.Open.pCoreOf 2 (P ⊔ J) ⊓ n155 A K ≤ CFSG.Open.pCoreOf 2 Y

@[expose] noncomputable def Step155CasesTwoWBig (A : Subgroup G) (c : G) (L : Subgroup G) :
    Prop :=
  Sec14Std G A c L → ∀ X K Y M T : Subgroup G, Ctx155 A X K Y M T → Big152 X →
    MaxT155 A X K T → Above155w A X → ∀ J ∈ thetaComponentsIn M, J ∈ scriptY0 A (lB A) →
    X ≤ J → (¬ ∃ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A ∧ L' ∈ lA A c' ∧
      L' = (L' ⊓ X) ⊔ CFSG.Open.pCoreOf 2 L') →
    ¬ (Case154Two L J X ∧ IsLThreePi (↥X ⧸ CFSG.pCore 2 ↥X))

@[expose] noncomputable def Step155CasesNWBig (A : Subgroup G) (c : G) (L : Subgroup G) : Prop :=
  Sec14Std G A c L → ∀ X K Y M T : Subgroup G, Ctx155 A X K Y M T → Big152 X →
    MaxT155 A X K T → Above155w A X → ∀ J ∈ thetaComponentsIn M, J ∈ scriptY0 A (lB A) →
    X ≤ J → ∃ P : Subgroup G, Data155N A L X Y M T P J

@[expose] noncomputable def Step155CasesTwoNHJWBig (A : Subgroup G) (c : G) (L : Subgroup G) :
    Prop :=
  Sec14Std G A c L → ¬ AllPointsHJ A → ∀ X K Y M T : Subgroup G, Ctx155 A X K Y M T →
    Big152 X → MaxT155 A X K T → Above155w A X → ∀ J ∈ thetaComponentsIn M,
    J ∈ scriptY0 A (lB A) → X ≤ J →
    (¬ ∃ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A ∧ L' ∈ lA A c' ∧
      L' = (L' ⊓ X) ⊔ CFSG.Open.pCoreOf 2 L') →
    ¬ (Case154Two L J X ∧ IsLThreePi (↥X ⧸ CFSG.pCore 2 ↥X))

end CFSG.RankThree.PartTwo.Sec15.Ronan155Big

namespace CFSG.RankThree.PartTwo.Sec15.Ronan155Big

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] noncomputable def Item155wBigR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Item155wBig A (lB A)

@[expose] noncomputable def Step155CasesTwoNHJWBigR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step155CasesTwoNHJWBig A c L

@[expose] noncomputable def DiamondBigR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ¬ AllPointsHJ A → ∀ X K Y M T : Subgroup G, Ctx155 A X K Y M T →
    Big152 X → MaxT155 A X K T → Above155w A X →
    (¬ ∃ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A ∧ L' ∈ lA A c' ∧
      L' = (L' ⊓ X) ⊔ CFSG.Open.pCoreOf 2 L') →
    K = X ⊔ CFSG.Open.pCoreOf 2 K →
    ∀ J ∈ thetaComponentsIn M, J ∈ scriptY0 A (lB A) → X ≤ J →
    ∀ n m : ℕ, 1 ≤ n → 1 ≤ m →
      Nonempty (↥J ⧸ CFSG.pCore 2 ↥J ≃*
        CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 (2 * n * m))) →
      IsLThreeEpsAt (↥X ⧸ CFSG.pCore 2 ↥X) 2 n → False

@[expose] noncomputable def DiamondCharBigR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ¬ AllPointsHJ A → ∀ X K Y M T : Subgroup G, Ctx155 A X K Y M T →
    Big152 X → MaxT155 A X K T → Above155w A X →
    (¬ ∃ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A ∧ L' ∈ lA A c' ∧
      L' = (L' ⊓ X) ⊔ CFSG.Open.pCoreOf 2 L') →
    K = X ⊔ CFSG.Open.pCoreOf 2 K →
    ∀ J ∈ thetaComponentsIn M, J ∈ scriptY0 A (lB A) → X ≤ J →
    ∀ n m : ℕ, 1 ≤ n → 1 ≤ m →
      Nonempty (↥J ⧸ CFSG.pCore 2 ↥J ≃*
        CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 (2 * n * m))) →
      IsLThreeEpsAt (↥X ⧸ CFSG.pCore 2 ↥X) 2 n →
      ∃ C : Subgroup G, C ≠ ⊥ ∧ C ≤ CFSG.Open.pCoreOf 2 Y ∧
        (C.subgroupOf (CFSG.Open.pCoreOf 2 Y)).Characteristic ∧
        J ≤ Subgroup.normalizer (C : Set G)

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {LB : Subgroup G → Subgroup G}

theorem item155wJ2_of_item155wBig (h : Item155wBig A LB) : Item155wJ2 A LB :=
  fun Y hY hX hb hYX K hK _ hhyp M hM => (h Y hY hX hb hYX).2 K hK hhyp M hM

theorem item155wJ2R_of_item155wBigR (h : Item155wBigR) : Item155wJ2R :=
  fun G _ _ A c L hR => item155wJ2_of_item155wBig (h G A c L hR)

end CFSG.RankThree.PartTwo.Sec15.Ronan155Big
