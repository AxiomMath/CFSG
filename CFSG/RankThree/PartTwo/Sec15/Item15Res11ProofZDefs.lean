module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec15.HypR
public import CFSG.RankThree.PartTwo.Sec15.Item1523Proof

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] noncomputable def Step1523ZPick : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ Y ∈ scriptY0Star A (lB A), ¬ MeetsY4 A (lB A) L Y → ∀ d : G, Data1523 A L Y d →
      CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer ({d} : Set G) = ⊥ →
      ∃ b ∈ A, b ∉ Subgroup.zpowers d ∧
        ∃ S : Subgroup G, S ≤ Y ⊓ Subgroup.centralizer ({b} : Set G) ∧ IsPGroup 2 S ∧
          A ≤ Subgroup.normalizer (S : Set G) ∧ ¬ S ≤ CFSG.Open.pCoreOf 2 Y

@[expose] noncomputable def Step1523ZLoc : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
    omegaA A ≠ {Subgroup.zpowers c} →
    ∀ d ∈ A, d ≠ 1 → IsThreeCentralIn L d →
    ∀ S : Subgroup G, S ≤ Subgroup.centralizer ({c} : Set G) → IsPGroup 2 S →
      A ≤ Subgroup.normalizer (S : Set G) →
        S ⊓ Subgroup.centralizer ({d} : Set G) ≤ Subgroup.centralizer (S : Set G)

@[expose] def KS1523HJTwo : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (L E S : Subgroup H) (z : H),
    Nonempty (↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
    E ≤ L → Nat.card E = 9 → z ∈ E → z ≠ 1 → IsThreeCentralIn L z →
    IsPGroup 2 S → S ≤ Subgroup.normalizer (L : Set H) →
    S ⊓ Subgroup.centralizer (L : Set H) = ⊥ → E ≤ Subgroup.normalizer (S : Set H) →
      S ⊓ Subgroup.centralizer ({z} : Set H) ≤ Subgroup.centralizer (S : Set H)

end CFSG.RankThree.PartTwo.Sec15
