module

public import CFSG.RankThree.GF2n.Tim81.Sec8.Assembly
public import CFSG.GroupTheory.TISylowLocal
public import CFSG.Timmesfeld.Bridge.Asc72Bender
public import CFSG.RankThree.PartOne.S15K.ProjSLBridge
public import CFSG.Open.PGLModelStated
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
public import CFSG.Models.BenderSuzuki
public import CFSG.StronglyEmbedded.Catalog.Suzuki
public import CFSG.CharacterTheory.Burnside
public import CFSG.Timmesfeld.Bridge.RootSetsSyl
public import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.GH74.SectionalRank
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.GroupTheory.HuppertProduct.Quotient
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.GF2n.Statements
public import CFSG.RankThree.GF2n.Tim77TI
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.S10.Defs
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec14.Std
public import CFSG.RankThree.PartTwo.Sec8.Pairs
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.Timmesfeld.Bridge.LocalA
public import CFSG.Timmesfeld.Bridge.NoPolarConnected
public import CFSG.Timmesfeld.Bridge.RootSets
public import CFSG.Timmesfeld.Bridge.RootSetsCases
public import CFSG.Timmesfeld.Bridge.RootSetsKernel
public import CFSG.Timmesfeld.Exceptional.Residual
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore
public import Certificates.Certificate43

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.BenderSuzuki CFSG.Timmesfeld.Bridge CFSG.GroupTheory CFSG.CGT.Timmesfeld75
open CFSG.Assembly.RankThreeEven (projSL projSU)

private noncomputable def projSL2EquivPSL2Model (n : ℕ) :
    projSL 2 (GaloisField 2 n) ≃* PSL2Model n :=
  (CFSG.RankThree.PartOne.S15K.projSLEquivProjectiveSL 2 (GaloisField 2 n)).trans
    (QuotientGroup.quotientMulEquivOfEq
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 2 (GaloisField 2 n)))

private noncomputable def projSU3EquivPSU3Model (n : ℕ) :
    projSU 3 2 n ≃* PSU3Model n :=
  ((CFSG.PGLModel.projSUEquivStatedProj 3 2 n).trans
      (CFSG.ShultStronglyClosedTI.glaSUCanonicalEquivNative n)).trans
    (MulEquiv.subgroupCongr (CFSG.Models.benderPSU3Model_eq_psu3 n).symm)

private noncomputable def suzukiCatEquivSzModel (m : ℕ)
    (hm : (TauCeti.LieTypeIndex.suzuki m).Valid) :
    (TauCeti.CFSGIndex.lie ⟨.suzuki m, hm⟩).Group ≃* SzModel m :=
  (CFSG.BenderSuzuki.Catalog.groupEquivSuzukiMatrixGroup hm).trans
    (MulEquiv.subgroupCongr (CFSG.BenderSuzuki.szModel_eq_suzukiMatrixGroup m).symm)

private theorem isTI_sylow_of_psl2 {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {n : ℕ} (hn : 1 ≤ n)
    (e : G ≃* projSL 2 (GaloisField 2 n)) (Q : Sylow 2 G) : IsTI (Q : Subgroup G) := by
  by_cases hn1 : n = 1
  · exfalso
    subst hn1
    have hcard : Nat.card G = 6 := by
      rw [Nat.card_congr (e.trans (projSL2EquivPSL2Model 1)).toEquiv,
        CFSG.Timmesfeld.Bridge.card_psl_two_galoisField_two 1 (by norm_num)]
      norm_num
    have hsolv : Group.IsSolvable G := by
      haveI : Fintype G := Fintype.ofFinite G
      exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
        (p := 2) (q := 3) (a := 1) (b := 1) Nat.prime_two Nat.prime_three (by norm_num)
        (by rw [← Nat.card_eq_fintype_card, hcard]; norm_num)
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hsolv a b)
  · have hn2 : 2 ≤ n := Nat.succ_le_of_lt (lt_of_le_of_ne hn (Ne.symm hn1))
    have hB : IsBenderGroup G :=
      IsBenderGroup.isPSL2 n hn2 (e.trans (projSL2EquivPSL2Model n))
    exact isTI_of_isStronglyEmbeddedOrder_normalizer
      (CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isStronglyEmbeddedOrder_normalizer hB Q)

private theorem isTI_sylow_of_psu3 {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {n : ℕ} (hn : 1 ≤ n)
    (e : G ≃* projSU 3 2 n) (Q : Sylow 2 G) : IsTI (Q : Subgroup G) := by
  by_cases hn1 : n = 1
  · exfalso
    subst hn1
    have hcard : Nat.card G = 72 := by
      rw [Nat.card_congr e.toEquiv]
      have h := CFSG.RankThree.PartTwo.KFacts.KS14.card_projSU_three_mul_gcd
        (p := 2) (f := 1) le_rfl
      norm_num at h
      omega
    have hsolv : Group.IsSolvable G := by
      haveI : Fintype G := Fintype.ofFinite G
      exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
        (p := 2) (q := 3) (a := 3) (b := 2) Nat.prime_two Nat.prime_three (by norm_num)
        (by rw [← Nat.card_eq_fintype_card, hcard]; norm_num)
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hsolv a b)
  · have hn2 : 2 ≤ n := Nat.succ_le_of_lt (lt_of_le_of_ne hn (Ne.symm hn1))
    have hB : IsBenderGroup G :=
      IsBenderGroup.isPSU3 n hn2 (e.trans (projSU3EquivPSU3Model n))
    exact isTI_of_isStronglyEmbeddedOrder_normalizer
      (CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isStronglyEmbeddedOrder_normalizer hB Q)

private theorem isTI_sylow_of_suzuki {G : Type} [Group G] [Finite G] {m : ℕ}
    (hm : (TauCeti.LieTypeIndex.suzuki m).Valid)
    (e : G ≃* (TauCeti.CFSGIndex.lie ⟨.suzuki m, hm⟩).Group) (Q : Sylow 2 G) :
    IsTI (Q : Subgroup G) := by
  have hm1 : 1 ≤ m := by
    have h := ((TauCeti.LieTypeIndex.valid_iff _).1 hm).1
    simpa [TauCeti.LieTypeIndex.inStandardRange_iff] using h
  have hB : IsBenderGroup G :=
    IsBenderGroup.isSuzuki m hm1 (e.trans (suzukiCatEquivSzModel m hm))
  exact isTI_of_isStronglyEmbeddedOrder_normalizer
      (CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isStronglyEmbeddedOrder_normalizer hB Q)

theorem sec8RankOneStatement : Sec8RankOneStatement := by
  intro G _ _ _ hnonab _ _ M V hHyp _ hwcQ hnwc _ hsyl hcase
  obtain ⟨T, hTM, -⟩ := hsyl.exists_sylow
  have hTI : IsTI (T : Subgroup G) := by
    rcases hcase with ⟨n, hn, hL2 | hU3⟩ | ⟨m, hm, hSz⟩
    · obtain ⟨e⟩ := hL2
      exact isTI_sylow_of_psl2 hnonab hn e T
    · obtain ⟨e⟩ := hU3
      exact isTI_sylow_of_psu3 hnonab hn e T
    · obtain ⟨e⟩ := hSz
      exact isTI_sylow_of_suzuki hm e T
  exact hnwc (weaklyClosedIn_of_isTI_sylow hnonab hHyp.maxLocal hTM hTI hHyp.maxAb.1.1 hwcQ)

end CFSG.RankThree.GF2n.Tim81
