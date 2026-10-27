module

public import CFSG.Assembly.InCatalog
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadicRank
public import CFSG.LocalAnalysis.AGLEmbedding.AltOuterOdd
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderPSU
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9

public section

namespace CFSG.StandardType.FF81.CatQ1

open CFSG.HardMathSupport.Timmesfeld.Coordinator
open CFSG.ComponentClassification.OuterAutomorphisms

private theorem exists_conj_of_card_outer_not_three_dvd {K G : Type*} [Group K] [Group G]
    (e : K ≃* G) (β : MulAut K) (hβ : β ^ 3 = 1)
    (h3 : ¬ 3 ∣ Nat.card (Outer G)) :
    ∃ k : K, β = MulAut.conj k := by
  let α : MulAut G := MulAut.congr e β
  have hα3 : α ^ 3 = 1 := by
    change (MulAut.congr e β) ^ 3 = 1
    rw [← map_pow, hβ, map_one]
  let q : Outer G := QuotientGroup.mk' (inner G) α
  have hq3 : q ^ 3 = 1 := by
    change (QuotientGroup.mk' (inner G) α : Outer G) ^ 3 = 1
    rw [← map_pow, hα3, map_one]
  have hq_dvd_three : orderOf q ∣ 3 := orderOf_dvd_of_pow_eq_one hq3
  have hq_dvd_card : orderOf q ∣ Nat.card (Outer G) := orderOf_dvd_natCard q
  have hcop : Nat.Coprime 3 (Nat.card (Outer G)) :=
    Nat.prime_three.coprime_iff_not_dvd.2 h3
  have hdvd_one : orderOf q ∣ 1 := by
    have hgcd : orderOf q ∣ Nat.gcd 3 (Nat.card (Outer G)) :=
      Nat.dvd_gcd hq_dvd_three hq_dvd_card
    rwa [hcop] at hgcd
  have hq_one : q = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 hdvd_one)
  have hα_inner : α ∈ inner G := by
    refine (QuotientGroup.eq_one_iff α).1 ?_
    simpa [q] using hq_one
  have hβ_inner : β ∈ inner K :=
    CFSG.HardMathSupport.Lang.Coordinator.congr_mem_inner_iff e β |>.1 hα_inner
  obtain ⟨k, hk⟩ := hβ_inner
  exact ⟨k, hk.symm⟩

theorem exists_conj_of_alternating {K : Type} [Group K] [Finite K] {n : ℕ} (hn : 5 ≤ n)
    (e : K ≃* (TauCeti.CFSGIndex.alternating n hn).Group) (β : MulAut K) (hβ : β ^ 3 = 1) :
    ∃ k : K, β = MulAut.conj k := by
  refine exists_conj_of_card_outer_not_three_dvd e β hβ ?_
  intro h3
  have h4 : Nat.card (Outer (TauCeti.CFSGIndex.alternating n hn).Group) ∣ 4 := by
    simpa using CFSG.AGLEmbedding.card_outer_alternatingGroup_dvd_four n hn
  exact absurd (h3.trans h4) (by norm_num)

theorem exists_conj_of_sporadic (hsp : SporadicOuterLeTwo) {K : Type} [Group K] [Finite K]
    [IsSimpleGroup K] (hnab : ∃ x y : K, x * y ≠ y * x) {s : TauCeti.SporadicName}
    (e : K ≃* (TauCeti.CFSGIndex.sporadic s).Group) (β : MulAut K) (hβ : β ^ 3 = 1) :
    ∃ k : K, β = MulAut.conj k := by
  refine exists_conj_of_card_outer_not_three_dvd e β hβ ?_
  have hout : Nat.card (Outer K) ≤ 2 := hsp K ‹IsSimpleGroup K› hnab s ⟨e⟩
  have hcard : Nat.card (Outer (TauCeti.CFSGIndex.sporadic s).Group) = Nat.card (Outer K) :=
    (Nat.card_congr (equivalence e).toEquiv).symm
  have hle : Nat.card (Outer (TauCeti.CFSGIndex.sporadic s).Group) ≤ 2 := hcard.trans_le hout
  have hpos : 0 < Nat.card (Outer (TauCeti.CFSGIndex.sporadic s).Group) := by
    rw [hcard]
    have hfinAut : Finite (MulAut K) := FunLike.finite (G := MulAut K)
    have hfinOuter : Finite (Outer K) :=
      @Finite.of_surjective (MulAut K) (Outer K) hfinAut (QuotientGroup.mk' (inner K))
        (QuotientGroup.mk'_surjective (N := inner K))
    have hne : Nonempty (Outer K) := ⟨1⟩
    exact Nat.card_pos_iff.2 ⟨hne, hfinOuter⟩
  intro h3
  have h3le : 3 ≤ Nat.card (Outer (TauCeti.CFSGIndex.sporadic s).Group) :=
    Nat.le_of_dvd hpos h3
  omega

end CFSG.StandardType.FF81.CatQ1
