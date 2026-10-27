module

import CFSG.CGT.PushingUp.TwoLocals
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.RankThree.PartTwo.Sec16.Item162Proof

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

@[expose] def Step162UJOdd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y₁ Y₂ S₁ S₂ : Subgroup G, MaxCE162 A (lB A) Y₁ Y₂ S₁ S₂ →
      ¬ S₁ ≤ S₂ → ¬ S₂ ≤ S₁ →
      ¬ TransOn A (lB A) (xA A)
          (delta A (lB A) (Subgroup.normalizer ((S₁ ⊓ S₂ : Subgroup G) : Set G))) →
      ∀ J₀ ∈ scriptY0 A (lB A),
        J₀ ∈ thetaComponentsIn
          (delta A (lB A) (Subgroup.normalizer ((S₁ ⊓ S₂ : Subgroup G) : Set G))) →
        (∃ n : ℕ, 1 ≤ n ∧ Sec4.IsoLThreePi (↥J₀ ⧸ CFSG.pCore 2 ↥J₀) 2 n) →
        (¬ ∃ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A ∧ L' ∈ lA A c' ∧
          L' = (L' ⊓ J₀) ⊔ CFSG.Open.pCoreOf 2 L') →
        ∃ J ∈ scriptY0 A (lB A),
          J ≤ delta A (lB A) (Subgroup.normalizer ((S₁ ⊓ S₂ : Subgroup G) : Set G)) ∧
            ¬ ∃ n : ℕ, 1 ≤ n ∧ Sec4.IsoLThreePi (↥J ⧸ CFSG.pCore 2 ↥J) 2 n

namespace Res162c

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

theorem normalizer_mem_scriptY2_and_fitting (hsimp : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hchar : CFSG.Assembly.IsCharTwoType G) {U : Subgroup G}
    (hU2 : IsPGroup 2 U) (hU1 : U ≠ ⊥) (hAU : A ≤ Subgroup.normalizer (U : Set G)) :
    Subgroup.normalizer (U : Set G) ∈ scriptY2 A ∧
      generalizedFitting ↥(Subgroup.normalizer (U : Set G)) =
        CFSG.pCore 2 ↥(Subgroup.normalizer (U : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := Subgroup.normalizer (U : Set G) with hN
  have hUO : U ≤ CFSG.Open.pCoreOf 2 N :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hU2
  refine ⟨⟨⟨normalizer_ne_top_of_isPGroup hsimp hnab hU1 hU2, hAU.trans Subgroup.le_normalizer⟩,
    fun h0 => hU1 (le_bot_iff.mp (h0 ▸ hUO))⟩, ?_⟩
  exact (isCharacteristicP_iff_generalizedFitting_eq_pCore ↥N 2).mp
    (CFSG.CGT.PushingUp.isCharacteristicP_of_isPLocal hchar
      (CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup hU2 hU1))

end Res162c

end CFSG.RankThree.PartTwo.Sec16
