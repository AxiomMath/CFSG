module

public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeSU
public import CFSG.Open.Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.GroupActions.SubgroupStabilizerOuterBound
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.TopScalarLiftSquare
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication

public section

namespace CFSG.StandardType.SCFourCover

open CFSG.LieType.Universal.Unitary (SU)
open CFSG.LieType.BorelTits (unitaryInvolution)

@[expose] def GGInnerOn {G : Type*} [Group G] (J : Subgroup G) (t : MulAut G) : Prop :=
  ∃ z ∈ J, ∀ j ∈ J, t j = z * j * z⁻¹

@[expose] def GGUnitaryOn {G : Type} [Group G] (J : Subgroup G) (t : MulAut G) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (f k : ℕ),
    Nat.card F = (2 ^ f) ^ 2 ∧ 1 ≤ f ∧ 2 ≤ k ∧ (k ≤ 3 → 2 ≤ f) ∧
    ∃ φ : ↥(SU (unitaryInvolution F 2 f) k) →* ↥J, Function.Surjective φ ∧
      φ.ker ≤ Subgroup.center ↥(SU (unitaryInvolution F 2 f) k) ∧
      ∃ (A : GL (Fin k) F) (hA : InnerDiagSU.IsJUnitary (unitaryInvolution F 2 f) A),
        ∀ B, t (φ B) = (φ (InnerDiagSU.conjSU A hA B) : G)

@[expose] def GGInnerOrUnitaryOnComps (G : Type) [Group G] : Prop :=
  ∀ x y : G, x ^ 3 = 1 → x ≠ 1 → y ^ 3 = 1 → x * y = y * x →
    ∀ J : Subgroup G, CFSG.Open.IsComponentOf J
        (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj x)) →
      MulAut.conj y ∈ CFSG.GroupActions.subgroupStabAut J →
      GGInnerOn J (MulAut.conj y) ∨ GGUnitaryOn J (MulAut.conj y)

end CFSG.StandardType.SCFourCover

end
