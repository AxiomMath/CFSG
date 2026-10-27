module

public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.Defs
import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderPSU
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
import CFSG.LieType.Ree.SuzukiSimple
import CFSG.LieType.Universal.SpinOmega.Range
import CFSG.LinearAlgebra.LinearGroups.CoordinateData
import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
import CFSG.LocalAnalysis.ComponentClassification.KProper
import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
import Certificates.Certificate1
import Certificates.Certificate10
import Certificates.Certificate11
import Certificates.Certificate12
import Certificates.Certificate2
import Certificates.Certificate3
import Certificates.Certificate4
import Certificates.Certificate42
import Certificates.Certificate44
import Certificates.Certificate5
import Certificates.Certificate6
import Certificates.Certificate7
import Certificates.Certificate8
import Certificates.Certificate9

public section

namespace CFSG.StandardType.FF81.CatQ1

open CFSG.Open
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

private theorem congr_apply_apply {G H : Type} [Group G] [Group H] (e : G ≃* H) (β : MulAut G)
    (x : H) : (MulAut.congr e β) x = e (β (e.symm x)) := rfl

theorem fixedTooBig_congr {K K' : Type} [Group K] [Group K'] (e : K ≃* K') (β : MulAut K) :
    FixedTooBig (MulAut.congr e β) ↔ FixedTooBig β := by
  have hcard : Nat.card (fixedSubgroup (MulAut.congr e β)) = Nat.card (fixedSubgroup β) :=
    CFSG.HardMathSupport.Lang.Coordinator.card_fixedSubgroup_congr e β
  have hiff : (∃ x : K', (MulAut.congr e β) x = x ∧ orderOf x = 9) ↔
      (∃ x : K, β x = x ∧ orderOf x = 9) := by
    constructor
    · rintro ⟨x, hx, ho⟩
      refine ⟨e.symm x, ?_, ?_⟩
      · apply e.injective
        rw [← congr_apply_apply e β x, hx, e.apply_symm_apply]
      · rw [MulEquiv.orderOf_eq e.symm x, ho]
    · rintro ⟨x, hx, ho⟩
      refine ⟨e x, ?_, ?_⟩
      · rw [congr_apply_apply e β (e x), e.symm_apply_apply, hx]
      · rw [MulEquiv.orderOf_eq e x, ho]
  simp only [FixedTooBig, hcard, hiff]

theorem OuterThreeBig.of_mulEquiv {K K' : Type} [Group K] [Finite K] [Group K'] [Finite K']
    (e : K ≃* K') (h : OuterThreeBig K) : OuterThreeBig K' := by
  intro hrank β' hβ'3 hβ'outer
  let β : MulAut K := MulAut.congr e.symm β'
  have hβ3 : β ^ 3 = 1 := by
    change ((MulAut.congr e.symm) β') ^ 3 = 1
    rw [← map_pow (MulAut.congr e.symm) β' 3, hβ'3, map_one]
  have hβouter : ∀ k : K, β ≠ MulAut.conj k := by
    intro k hk
    have hmem : β ∈ inner K := by
      rw [hk]
      exact ⟨k, rfl⟩
    obtain ⟨k', hk'⟩ :=
      (CFSG.HardMathSupport.Lang.Coordinator.congr_mem_inner_iff e.symm β').mp hmem
    exact hβ'outer k' hk'.symm
  have hrankK : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K) := by
    rwa [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (show 1 < 3 by norm_num) e.symm] at hrank
  have hβ : FixedTooBig β := h hrankK β hβ3 hβouter
  exact (fixedTooBig_congr e.symm β').mp hβ

end CFSG.StandardType.FF81.CatQ1
