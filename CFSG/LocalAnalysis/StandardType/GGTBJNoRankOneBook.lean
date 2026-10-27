module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
import CFSG.LocalAnalysis.StandardType.GGNbrBalance
import CFSG.GroupTheory.PLayer.CenterQuotientAction
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
import CFSG.Dihedral.DihedralFusionPrefixes
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
import CFSG.LocalAnalysis.ComponentClassification.KProper
import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
import CFSG.LocalAnalysis.LargeEvenClassification.TopScalarLiftSquare
import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggRankOne_B_to_aut {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) :
    B ≤ Subgroup.normalizer (J : Set G) ∧
    ∃ φ : ↥B →* MulAut (↥J ⧸ Subgroup.center ↥J), Nat.card φ.ker = p ^ 2 ∧
      ∀ (b : ↥B) (j j' : ↥J), (b : G) * (j : G) * (b : G)⁻¹ = (j' : G) →
        φ b (j : ↥J ⧸ Subgroup.center ↥J) = (j' : ↥J ⧸ Subgroup.center ↥J) := by
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hst : LargeEvenStandardType p B x L := hcfg.1.2.2.2.2.2.2.2
  have hpre : LargeEvenStdSubPre p B x L D J := hcfg.2.2.1
  have hDB : D ≤ B := hpre.1
  have hDcard : Nat.card D = p ^ 2 := hpre.2.2.1
  have hcomp : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) := hpre.2.2.2.2.2.1
  have hDcent : D = B ⊓ Subgroup.centralizer (J : Set G) := hpre.2.2.2.2.2.2
  haveI hperfJ : Group.IsPerfect ↥J := ⟨hcomp.2.2.1⟩
  have hnormJ : B ≤ Subgroup.normalizer (J : Set G) := le_normalizer_of_stdSub hS hst hpre
  refine ⟨hnormJ, CFSG.normalizerToCenterQuotientAut J B hnormJ, ?_, ?_⟩
  · rw [CFSG.ker_normalizerToCenterQuotientAut hperfJ hnormJ, ← hDcent, ← hDcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDB).toEquiv
  · intro b j j' hconj
    have hcoe : ((CFSG.normalizerConjAutOfMem J B hnormJ b j : ↥J) : G) = (j' : G) := by
      change ((J.normalizerMonoidHom (Subgroup.inclusion hnormJ b)) j : G) = (j' : G)
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      exact hconj
    have h := CFSG.normalizerConjAutOfMem_comp_mk J B hnormJ b j
    rw [show CFSG.normalizerConjAutOfMem J B hnormJ b j = j' from Subtype.ext hcoe] at h
    exact h.symm

end CFSG.StandardType

end
