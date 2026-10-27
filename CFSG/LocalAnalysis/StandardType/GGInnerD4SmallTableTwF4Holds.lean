module

public import CFSG.LocalAnalysis.StandardType.GGInnerD4SmallContracts
public import CFSG.LocalAnalysis.StandardType.GGL45FixA2Comp
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45FieldFixReeMark
import CFSG.LocalAnalysis.StandardType.GGTwF4FixOrderThree
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofReeConj
public import CFSG.RankThree.PartTwo.Sec8.Item87ProofGamma
public import CFSG.Fischer.Classification.Recognition.CaseR3
public import CFSG.LieType.Ree.LargeReeCenterTrivial
public import CFSG.HardMathSupport.Dickson.SuzukiReeB.Helpers
public import CFSG.HardMathSupport.Solomon.Coordinator.L3AFix
public import CFSG.Assembly.GL83StatedBridge
public import CFSG.HardMathSupport.Solomon.Coordinator.B3FamPC
public import CFSG.HardMathSupport.Solomon.Coordinator.L3ABridge
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.RankThree.PartTwo.Sec8.Steps

public section

namespace CFSG.StandardType.GGInnerD4SmallParts

open CFSG CFSG.Assembly CFSG.StandardType

private theorem ltrsm8_component_label
    (a : ℕ) (ha : 1 ≤ a)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (τ : MulAut (LargeEvenCenterQuot (LargeEvenTwF4H a K)))
    (hτI : τ ∈ LargeEvenChevIDImage LargeEvenCartanF4 K (LargeEvenTwF4H a K))
    (hτ3 : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    (L : Subgroup (LargeEvenCenterQuot (LargeEvenTwF4H a K)))
    (hL : IsComponentOf L (ggAutFixedSubgroup τ)) :
    GGHasLabel ⟨.twA, 2, 2 * a + 1⟩ (↥L ⧸ Subgroup.center ↥L) := by
  classical
  obtain ⟨eCent⟩ := twF4_ggAutFixedSubgroup_mulEquiv_unitarySU a ha K hK τ hτI hτ3 hτ1
  have hF : Nat.card (GaloisField 2 (2 * (2 * a + 1))) = (2 ^ (2 * a + 1)) ^ 2 := by
    rw [GaloisField.card 2 (2 * (2 * a + 1)) (by omega), mul_comm 2 (2 * a + 1), pow_mul]
  have hnq : (3, 2 ^ (2 * a + 1)) ≠ (3, 2) := by
    intro h
    have h2 : 2 ^ (2 * a + 1) = 2 := (Prod.mk.inj h).2
    have h4 : 4 ≤ 2 ^ (2 * a + 1) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSUZ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    (p := 2) (f := 2 * a + 1) (F := GaloisField 2 (2 * (2 * a + 1))) hF le_rfl hnq
  have hqC : CFSG.Open.IsQuasisimple ↥(ggAutFixedSubgroup τ) :=
    CFSG.HardMathSupport.Solomon.Coordinator.isQuasisimple_open
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv eCent.symm hSUZ.1)
  have hJopen : CFSG.Open.IsComponentOf L (ggAutFixedSubgroup τ) :=
    (CFSG.Assembly.isComponentOf_iff_open).1 hL
  have hLC : L = ggAutFixedSubgroup τ :=
    CFSG.Fischer.Classification.Recognition.IsComponentOf.eq_of_isQuasisimple hJopen hqC
  subst hLC
  simp only [GGHasLabel, CFSG.StandardType.LargeEvenRawDatum, LargeEvenRecipeUnitary]
  haveI hNs : ((CFSG.Open.StatedScalars (Fin (2 + 1))
      (GaloisField 2 (2 * (2 * a + 1)))).subgroupOf
      (CFSG.Open.StatedSU (2 + 1) (2 ^ (2 * a + 1))
        (GaloisField 2 (2 * (2 * a + 1))))).Normal :=
    Subgroup.normal_subgroupOf
  refine ⟨GaloisField 2 (2 * (2 * a + 1)), inferInstance, inferInstance, hF, ?_⟩
  show Nonempty (↥(ggAutFixedSubgroup τ) ⧸ Subgroup.center ↥(ggAutFixedSubgroup τ) ≃*
    CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ (2 * a + 1))
      (GaloisField 2 (2 * (2 * a + 1)))))
  exact ⟨(QuotientGroup.congr _ _ eCent (Subgroup.map_center_eq eCent)).trans
    (QuotientGroup.quotientMulEquivOfEq hSUZ.2)⟩

theorem smallTableTwF4_holds :
    ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → lab.tag = .twF4 →
      LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ =>
        ∀ τ : MulAut R, τ ∈ I → τ ^ 3 = 1 → τ ≠ 1 →
          ∀ L : Subgroup R, IsComponentOf L (ggAutFixedSubgroup τ) →
            ∃ out : LargeEvenLabel, LargeEvenInLambda2 out ∧
              S2MathAs51600Small.TableComponentLabel lab out ∧
              GGHasLabel out (↥L ⧸ Subgroup.center ↥L)) := by
  intro lab hlab ht
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht
  subst ht
  dsimp only [LargeEvenInLambda2] at hlab
  obtain ⟨-, hodd, h3⟩ := hlab.2
  intro Q hQ
  have h2a1 : 2 * ((n - 1) / 2) + 1 = n := by
    obtain ⟨k, hk⟩ := hodd
    have hn1 : n - 1 = 2 * k := by omega
    rw [hn1]
    omega
  have ha : 1 ≤ (n - 1) / 2 := by omega
  refine recipeTwF4_and (a := (n - 1) / 2) ?_ hQ
  intro K hfield hfin hK hsimple hna
  intro τ hτI hτ3 hτ1 L hL
  refine ⟨⟨.twA, 2, n⟩, ?_, ?_, ?_⟩
  · show 1 ≤ n ∧ 2 ≤ 2 ∧ (2 = 2 → 2 ≤ n)
    exact ⟨by omega, by norm_num, fun _ => by omega⟩
  · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · have hlab' := ltrsm8_component_label (a := (n - 1) / 2) (ha := ha) (K := K)
      hK τ hτI hτ3 hτ1 L hL
    rwa [h2a1] at hlab'

end CFSG.StandardType.GGInnerD4SmallParts

end
