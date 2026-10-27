module

public import CFSG.LocalAnalysis.StandardType.GGOmegaPlusRootGenDefs
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotGlobalGen
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2FieldDataWeyl
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRoots
import CFSG.CGT.Timmesfeld75.L2Pair
import CFSG.CGT.Timmesfeld75.ListWCBasic
import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
import CFSG.ClassicalGroups
import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcLevi
import CFSG.ClassicalInvolution.QuaternionStructure
import CFSG.ClassicalInvolution.WeakCT.Main
import CFSG.GH74.GLS.Defs
import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Closed
import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Statements
import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Defs
import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Ext
import CFSG.GH74.GLS.Stage2.Final.LayerFDerive
import CFSG.GH74.Statements
import CFSG.LieType.CurtisTits.Adjoint
import CFSG.LieType.Ree.LargeReeEightTorus
import CFSG.LieType.Ree.LargeReeInvolutionTwoCentralizers
import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenE6
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenTriality
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddE6
import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIL3Rigid
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupLinearThreeFour
import CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModelCases
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Five
import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviPerp
import CFSG.LocalAnalysis.SeitzReduction.E7PilotFieldNormalizeAutMain
import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2PositionWork
import CFSG.LocalAnalysis.SeitzReduction.E8PilotSwapLift
import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphE6
import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphTwistedXi
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassical
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenExc
import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndField
import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourFix
import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourLift
import CFSG.LocalAnalysis.SeitzReduction.F4PilotInnerField
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTwistedFusion
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotWeakCTGlobal
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotBLiftAniso
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatCovers
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotGlobalClass
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusClass
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusCoverHR8Global
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphOmegaNeighbour
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizeFieldFour
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotAlignImagesSwap
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUniqueTypeGraph
import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
import CFSG.Quasithin.Background.A1cTransfer
import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl
import CFSG.RankThree.Chevalley.SteinbergCFEvenF4PointwiseInner
import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.RankThree.PartOne.AUTSL.OmegaFamily
import CFSG.RankThree.PartOne.AUTSL.Rows
import CFSG.RankThree.PartOne.AUTSL.SylowTrick
import CFSG.RankThree.PartOne.CTP.StrongPSylow
import CFSG.RankThree.PartOne.KC.OrthogonalHighWittFixedSpace
import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeSetting
import CFSG.RankThree.PartOne.KC.UnitaryLiftBlocks
import CFSG.RankThree.PartOne.KF.UnitaryModel
import CFSG.RankThree.PartOne.S12.InputsBase
import CFSG.RankThree.PartOne.S12.Sec1511Y1
import CFSG.RankThree.PartOne.S12.Sec15Items
import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary
import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
import CFSG.Sporadic.Bridge.LyData
import CFSG.Sporadic.Fi24.Faithful
import CFSG.Sporadic.Fi24.SepSpec
import CFSG.Sporadic.HN.CertificateBase
import CFSG.Sporadic.Ly.ActionBase
import CFSG.Sporadic.Ly.CertificateBase
import CFSG.Sporadic.Ly.FaithSpec
import CFSG.Sporadic.Ly.OrbitSpec
import CFSG.Sporadic.Ly.Simple
import CFSG.Sporadic.LyBase
import CFSG.Sporadic.ON.SimpleBase
import CFSG.Sporadic.Presentation.Ly
import CFSG.Sporadic.Schreier.J4SProfileNode
import CFSG.Sporadic.Schreier.LyChain11
import CFSG.Sporadic.Schreier.TitsOther
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
import Certificates.Certificate10
import Certificates.Certificate1016Base
import Certificates.Certificate1021
import Certificates.Certificate11
import Certificates.Certificate12
import Certificates.Certificate3
import Certificates.Certificate3085Base
import Certificates.Certificate4
import Certificates.Certificate42
import Certificates.Certificate44
import Certificates.Certificate5
import Certificates.Certificate6
import Certificates.Certificate7
import Certificates.Certificate8
import Certificates.Certificate9

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.SeitzReduction
open CFSG.ClassicalInvolution.Models.SymplecticPairs (leviEmbedSL)

variable {K : Type} [Field K] {m : ℕ}

private noncomputable abbrev omPlusSpan (K : Type) [Field K] (m : ℕ) (x₀ : OmPlusIdx m) :
    Subgroup (GL (Fin m ⊕ Fin m) K) :=
  ⨆ (x : OmPlusIdx m) (_ : x ≠ x₀), omPlusBlock K x

private def idxPair (x : OmPlusIdx m) : Finset (Fin m) := {x.1.1.1, x.1.1.2}

private def unsignedIdx {a b : Fin m} (h : a ≠ b) : OmPlusIdx m :=
  if hab : a < b then
    (⟨(a, b), hab⟩, false)
  else
    have hba : b < a := by
      rcases lt_or_gt_of_ne h with h' | h'
      · exact absurd h' hab
      · exact h'
    (⟨(b, a), hba⟩, false)

private def idxOfTrue {a b : Fin m} (h : a < b) : OmPlusIdx m := (⟨(a, b), h⟩, true)

private theorem idxPair_unsignedIdx {a b : Fin m} (h : a ≠ b) :
    idxPair (unsignedIdx h) = ({a, b} : Finset (Fin m)) := by
  unfold unsignedIdx
  split_ifs with hab
  · rfl
  · exact Finset.pair_comm b a

private theorem idxPair_idxOfTrue {a b : Fin m} (h : a < b) :
    idxPair (idxOfTrue h) = ({a, b} : Finset (Fin m)) :=
  rfl

private theorem omPlusBlock_unsignedIdx {a b : Fin m} (h : a ≠ b) :
    omPlusBlock K (unsignedIdx h) =
      OmegaPilot.siegelBlockGL K ({a, b} : Finset (Fin m)) := by
  unfold unsignedIdx
  split_ifs with hab
  · exact omPlusBlock_false (K := K) hab
  · have hba : b < a := by
      rcases lt_or_gt_of_ne h with h' | h'
      · exact absurd h' hab
      · exact h'
    rw [omPlusBlock_false (K := K) hba, Finset.pair_comm]

private theorem unsignedIdx_ne_of_pair_ne {a b : Fin m} (h : a ≠ b) {x₀ : OmPlusIdx m}
    (hp : ({a, b} : Finset (Fin m)) ≠ idxPair x₀) : unsignedIdx h ≠ x₀ := by
  intro he
  apply hp
  rw [← idxPair_unsignedIdx h, he]

private theorem idxOfTrue_ne_of_pair_ne {a b : Fin m} (h : a < b) {x₀ : OmPlusIdx m}
    (hp : ({a, b} : Finset (Fin m)) ≠ idxPair x₀) : idxOfTrue h ≠ x₀ := by
  intro he
  apply hp
  rw [← idxPair_idxOfTrue h, he]

private theorem le_omPlusSpan_of_ne {x₀ x : OmPlusIdx m} (hx : x ≠ x₀) :
    omPlusBlock K x ≤ omPlusSpan K m x₀ :=
  le_iSup₂ (f := fun x (_ : x ≠ x₀) => omPlusBlock K x) x hx

private theorem siegelBlockGL_le_omPlusSpan {x₀ : OmPlusIdx m} {a b : Fin m} (h : a ≠ b)
    (hp : ({a, b} : Finset (Fin m)) ≠ idxPair x₀) :
    OmegaPilot.siegelBlockGL K ({a, b} : Finset (Fin m)) ≤ omPlusSpan K m x₀ := by
  rw [← omPlusBlock_unsignedIdx (K := K) h]
  exact le_omPlusSpan_of_ne (unsignedIdx_ne_of_pair_ne h hp)

private theorem map_conj_permSp_swap_siegelBlock [CharP K 2] {a b : Fin m}
    (B : Finset (Fin m)) :
    (SymplecticPilot.siegelBlock K B).map
        (MulAut.conj (SymplecticPilot.permSp K (Equiv.swap a b))).toMonoidHom =
      SymplecticPilot.siegelBlock K (B.map (Equiv.swap a b).toEmbedding) := by
  have hP : SymplecticPilot.permSp K (Equiv.swap a b) =
      leviEmbedSL K m (OmegaPilot.q2SwapSL a b) :=
    OmegaPilot.permSp_swap_eq a b
  have hcomp : (MulAut.conj (leviEmbedSL K m (OmegaPilot.q2SwapSL a b))).toMonoidHom.comp
        (leviEmbedSL K m) =
      (leviEmbedSL K m).comp (MulAut.conj (OmegaPilot.q2SwapSL a b)).toMonoidHom := by
    ext C
    simp [MulAut.conj_apply, map_mul]
  have hblk : (LinearPilot.blockSpecialLinear (K := K) B).map
        (MulAut.conj (OmegaPilot.q2SwapSL a b)).toMonoidHom =
      LinearPilot.blockSpecialLinear (B.map (Equiv.swap a b).toEmbedding) := by
    have h := LinearPilot.blockComplProj_mul_permMatrix (K := K) (Equiv.swap a b) B
    have hsymm : (Equiv.swap a b).symm = Equiv.swap a b := by
      rw [← Equiv.Perm.inv_def, Equiv.swap_inv]
    rw [hsymm] at h
    exact LinearPilot.map_conj_blockSpecialLinear_of_mul_eq (OmegaPilot.q2SwapSL a b) h
  rw [SymplecticPilot.siegelBlock, SymplecticPilot.siegelBlock, hP, Subgroup.map_map, hcomp,
    ← Subgroup.map_map, hblk]

private theorem map_conj_permSp_swap_siegelBlockGL [CharP K 2] {a b : Fin m}
    (B : Finset (Fin m)) :
    (OmegaPilot.siegelBlockGL K B).map
        (MulAut.conj ((SymplecticPilot.permSp K (Equiv.swap a b) : StatedSp m K) :
          GL (Fin m ⊕ Fin m) K)).toMonoidHom =
      OmegaPilot.siegelBlockGL K (B.map (Equiv.swap a b).toEmbedding) := by
  have hcomp : (MulAut.conj ((SymplecticPilot.permSp K (Equiv.swap a b) : StatedSp m K) :
        GL (Fin m ⊕ Fin m) K)).toMonoidHom.comp (StatedSp m K).subtype =
      (StatedSp m K).subtype.comp
        (MulAut.conj (SymplecticPilot.permSp K (Equiv.swap a b))).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply]
  rw [OmegaPilot.siegelBlockGL, OmegaPilot.siegelBlockGL, Subgroup.map_map, hcomp,
    ← Subgroup.map_map, map_conj_permSp_swap_siegelBlock]

private theorem siegelBlockGL_le_sup_pair [CharP K 2] {a b k : Fin m}
    (hab : a ≠ b) (hak : a ≠ k) (hkb : k ≠ b) :
    OmegaPilot.siegelBlockGL K ({a, b} : Finset (Fin m)) ≤
      OmegaPilot.siegelBlockGL K ({a, k} : Finset (Fin m)) ⊔
        OmegaPilot.siegelBlockGL K ({k, b} : Finset (Fin m)) := by
  have hconj := map_conj_permSp_swap_siegelBlockGL (K := K) (a := k) (b := b)
    ({a, k} : Finset (Fin m))
  have hswap_a : (Equiv.swap k b) a = a :=
    Equiv.swap_apply_of_ne_of_ne (a := k) (b := b) (x := a) hak hab
  have hswap_k : (Equiv.swap k b) k = b := Equiv.swap_apply_left k b
  have hmap : ({a, k} : Finset (Fin m)).map (Equiv.swap k b).toEmbedding = {a, b} := by
    rw [Finset.map_insert, Finset.map_singleton]
    change {(Equiv.swap k b) a, (Equiv.swap k b) k} = {a, b}
    rw [hswap_a, hswap_k]
  rw [hmap] at hconj
  rw [← hconj]
  rintro x ⟨y, hy, rfl⟩
  have hP : ((SymplecticPilot.permSp K (Equiv.swap k b) : StatedSp m K) :
      GL (Fin m ⊕ Fin m) K) ∈
      OmegaPilot.siegelBlockGL K ({k, b} : Finset (Fin m)) :=
    OmegaPilot.permSp_swap_mem_siegelBlockGL k b
  exact mul_mem (mul_mem (Subgroup.mem_sup_right hP) (Subgroup.mem_sup_left hy))
    (Subgroup.mem_sup_right (inv_mem hP))

private theorem flipBlock_le_sup_pair [CharP K 2] {a b k : Fin m}
    (hab : a ≠ b) (hak : a ≠ k) (hkb : k ≠ b) :
    (OmegaPilot.siegelBlockGL K ({a, b} : Finset (Fin m))).map
        (MulAut.conj (OmegaPilot.flipGL K ({b} : Finset (Fin m)))).toMonoidHom ≤
      OmegaPilot.siegelBlockGL K ({a, k} : Finset (Fin m)) ⊔
        (OmegaPilot.siegelBlockGL K ({k, b} : Finset (Fin m))).map
          (MulAut.conj (OmegaPilot.flipGL K ({b} : Finset (Fin m)))).toMonoidHom := by
  have hmap := Subgroup.map_mono
    (f := (MulAut.conj (OmegaPilot.flipGL K ({b} : Finset (Fin m)))).toMonoidHom)
    (siegelBlockGL_le_sup_pair (K := K) hab hak hkb)
  rw [Subgroup.map_sup] at hmap
  have hfix : (OmegaPilot.siegelBlockGL K ({a, k} : Finset (Fin m))).map
        (MulAut.conj (OmegaPilot.flipGL K ({b} : Finset (Fin m)))).toMonoidHom =
      OmegaPilot.siegelBlockGL K ({a, k} : Finset (Fin m)) := by
    refine OmegaPilot.map_flipGL_siegelBlockGL_of_disjoint (K := K) ?_
    rw [Finset.disjoint_left]
    intro x hx hb
    rw [Finset.mem_singleton] at hb
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hab hb
    · exact hkb hb
  rwa [hfix] at hmap

private theorem plusNodeSet_eq_pair {j : Fin m} (hj : j.val + 1 < m) :
    OmegaPilot.plusNodeSet m j = ({j, (⟨j.val + 1, hj⟩ : Fin m)} : Finset (Fin m)) := by
  ext x
  rw [OmegaPilot.mem_plusNodeSet, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (⟨-, hx | hx⟩ | ⟨h, -⟩)
    · exact Or.inl (Fin.ext hx)
    · exact Or.inr (Fin.ext hx)
    · omega
  · rintro (rfl | rfl)
    · exact Or.inl ⟨hj, Or.inl rfl⟩
    · exact Or.inl ⟨hj, Or.inr rfl⟩

private theorem plusNodeFlip_eq_empty {j : Fin m} (hj : j.val + 1 < m) :
    OmegaPilot.plusNodeFlip m j = ∅ := by
  ext x
  rw [OmegaPilot.mem_plusNodeFlip]
  simp only [Finset.notMem_empty, iff_false, not_and]
  omega

private theorem plusNodeSet_eq_last (hm : 4 ≤ m) {j : Fin m} (hj : j.val + 1 = m) :
    OmegaPilot.plusNodeSet m j =
      ({(⟨m - 2, by omega⟩ : Fin m), (⟨m - 1, by omega⟩ : Fin m)} : Finset (Fin m)) := by
  ext x
  rw [OmegaPilot.mem_plusNodeSet, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (⟨h, -⟩ | ⟨-, hx⟩)
    · omega
    · have hxlt := x.isLt
      have hx' : x.val = m - 2 ∨ x.val = m - 1 := by omega
      rcases hx' with h' | h'
      · exact Or.inl (Fin.ext h')
      · exact Or.inr (Fin.ext h')
  · rintro (rfl | rfl)
    · exact Or.inr ⟨hj, by
        change m ≤ m - 2 + 2
        omega⟩
    · exact Or.inr ⟨hj, by
        change m ≤ m - 1 + 2
        omega⟩

private theorem plusNodeFlip_eq_last {j : Fin m} (hj : j.val + 1 = m) :
    OmegaPilot.plusNodeFlip m j =
      ({(⟨m - 1, by omega⟩ : Fin m)} : Finset (Fin m)) := by
  ext x
  rw [OmegaPilot.mem_plusNodeFlip, Finset.mem_singleton]
  constructor
  · rintro ⟨-, hx⟩
    exact Fin.ext (by
      change x.val = m - 1
      omega)
  · rintro rfl
    exact ⟨hj, by
      change m - 1 + 1 = m
      omega⟩

theorem statedOmega_quadPlus_le_iSup_omPlusBlock_ne {K : Type} [Field K] [Finite K]
    [CharP K 2] {m f : ℕ} (hm : 4 ≤ m) (hKf : Nat.card K = 2 ^ f)
    (hK : 4 ≤ Nat.card K) (x₀ : OmPlusIdx m) :
    StatedOmega (StatedQuadPlus m K) ≤ ⨆ (x : OmPlusIdx m) (_ : x ≠ x₀), omPlusBlock K x := by
  classical
  change StatedOmega (StatedQuadPlus m K) ≤ omPlusSpan K m x₀
  rw [← OmegaPilot.iSup_siegelNode_eq_statedOmega (K := K) (n := m) (f := f) hm hKf hK]
  apply iSup_le
  intro j
  by_cases hj : j.val + 1 < m
  ·
    set j1 : Fin m := ⟨j.val + 1, hj⟩ with hj1
    have hj1val : j1.val = j.val + 1 := by
      rw [hj1]
    have hjlt : j < j1 := by
      rw [Fin.lt_def, hj1val]
      omega
    have hset : OmegaPilot.plusNodeSet m j = ({j, j1} : Finset (Fin m)) := by
      rw [plusNodeSet_eq_pair hj, ← hj1]
    have hflip : OmegaPilot.plusNodeFlip m j = ∅ := plusNodeFlip_eq_empty hj
    have hnode : OmegaPilot.siegelNode K m j =
        OmegaPilot.siegelBlockGL K ({j, j1} : Finset (Fin m)) := by
      rw [OmegaPilot.siegelNode, hset, hflip, OmegaPilot.flipGL_empty,
        OmegaPilot.map_conj_one_eq]
    have hk_exists : ∃ k : Fin m, k ≠ j ∧ k ≠ j1 := by
      by_cases hj0 : j.val = 0
      · refine ⟨⟨2, by omega⟩, ?_, ?_⟩
        · intro h
          have h' : (2 : ℕ) = j.val := congrArg Fin.val h
          omega
        · intro h
          have h' : (2 : ℕ) = j.val + 1 := by
            simpa [hj1val] using congrArg Fin.val h
          omega
      · refine ⟨⟨0, by omega⟩, ?_, ?_⟩
        · intro h
          have h' : (0 : ℕ) = j.val := congrArg Fin.val h
          omega
        · intro h
          have h' : (0 : ℕ) = j.val + 1 := by
            simpa [hj1val] using congrArg Fin.val h
          omega
    obtain ⟨k, hkj, hkj1⟩ := hk_exists
    by_cases hx : unsignedIdx (a := j) (b := j1) (ne_of_lt hjlt) = x₀
    ·
      have hpair₀ : idxPair x₀ = ({j, j1} : Finset (Fin m)) := by
        rw [← hx, idxPair_unsignedIdx]
      have hknot : k ∉ ({j, j1} : Finset (Fin m)) := by
        simp [hkj, hkj1]
      have hp1 : ({j, k} : Finset (Fin m)) ≠ idxPair x₀ := by
        intro he
        apply hknot
        rw [← hpair₀, ← he]
        simp
      have hp2 : ({k, j1} : Finset (Fin m)) ≠ idxPair x₀ := by
        intro he
        apply hknot
        rw [← hpair₀, ← he]
        simp
      have hgen := siegelBlockGL_le_sup_pair (K := K) (a := j) (b := j1) (k := k)
        (ne_of_lt hjlt) hkj.symm hkj1
      rw [hnode]
      refine hgen.trans (sup_le ?_ ?_)
      · exact siegelBlockGL_le_omPlusSpan (K := K) (x₀ := x₀) (a := j) (b := k)
          hkj.symm hp1
      · exact siegelBlockGL_le_omPlusSpan (K := K) (x₀ := x₀) (a := k) (b := j1) hkj1 hp2
    ·
      rw [hnode, ← omPlusBlock_unsignedIdx (K := K) (a := j) (b := j1) (ne_of_lt hjlt)]
      exact le_omPlusSpan_of_ne hx
  ·
    have hjlast : j.val + 1 = m := by
      have := j.isLt
      omega
    set a : Fin m := ⟨m - 2, by omega⟩ with ha
    set b : Fin m := ⟨m - 1, by omega⟩ with hb
    have hab : a < b := by
      rw [Fin.lt_def]
      change a.val < b.val
      rw [show a.val = m - 2 from by rw [ha], show b.val = m - 1 from by rw [hb]]
      omega
    have hset : OmegaPilot.plusNodeSet m j = ({a, b} : Finset (Fin m)) := by
      rw [plusNodeSet_eq_last hm hjlast, ← ha, ← hb]
    have hflip : OmegaPilot.plusNodeFlip m j = ({b} : Finset (Fin m)) := by
      rw [plusNodeFlip_eq_last hjlast, ← hb]
    have hnode : OmegaPilot.siegelNode K m j =
        (OmegaPilot.siegelBlockGL K ({a, b} : Finset (Fin m))).map
          (MulAut.conj (OmegaPilot.flipGL K ({b} : Finset (Fin m)))).toMonoidHom := by
      rw [OmegaPilot.siegelNode, hset, hflip]
    by_cases hx : idxOfTrue hab = x₀
    ·
      set z : Fin m := ⟨0, by omega⟩ with hz
      have hzero : z ≠ a := by
        intro h
        have h' : (0 : ℕ) = a.val := congrArg Fin.val h
        have h'' : (0 : ℕ) = m - 2 := by simpa [ha] using h'
        omega
      have hzero' : z ≠ b := by
        intro h
        have h' : (0 : ℕ) = b.val := congrArg Fin.val h
        have h'' : (0 : ℕ) = m - 1 := by simpa [hb] using h'
        omega
      have hza : z < a := by
        rw [Fin.lt_def]
        change z.val < a.val
        rw [show z.val = (0 : ℕ) from rfl, show a.val = m - 2 from by rw [ha]]
        omega
      have hzb : z < b := by
        rw [Fin.lt_def]
        change z.val < b.val
        rw [show z.val = (0 : ℕ) from rfl, show b.val = m - 1 from by rw [hb]]
        omega
      have hpair₀ : idxPair x₀ = ({a, b} : Finset (Fin m)) := by
        rw [← hx, idxPair_idxOfTrue]
      have hp1 : ({a, z} : Finset (Fin m)) ≠ idxPair x₀ := by
        intro he
        have h' : z ∈ ({a, b} : Finset (Fin m)) := by
          rw [← hpair₀, ← he]
          simp
        rw [Finset.mem_insert, Finset.mem_singleton] at h'
        rcases h' with h' | h'
        · exact hzero h'
        · exact hzero' h'
      have hp2 : ({z, b} : Finset (Fin m)) ≠ idxPair x₀ := by
        intro he
        have h' : z ∈ ({a, b} : Finset (Fin m)) := by
          rw [← hpair₀, ← he]
          simp
        rw [Finset.mem_insert, Finset.mem_singleton] at h'
        rcases h' with h' | h'
        · exact hzero h'
        · exact hzero' h'
      have hgen := flipBlock_le_sup_pair (K := K) (a := a) (b := b) (k := z)
        (ne_of_lt hab) (ne_of_gt hza) hzero'
      rw [hnode]
      refine hgen.trans (sup_le ?_ ?_)
      · exact siegelBlockGL_le_omPlusSpan (K := K) (x₀ := x₀) (a := a) (b := z)
          (ne_of_gt hza) hp1
      · rw [← omPlusBlock_true (K := K) hzb]
        exact le_omPlusSpan_of_ne (idxOfTrue_ne_of_pair_ne hzb hp2)
    · rw [hnode, ← omPlusBlock_true (K := K) hab]
      exact le_omPlusSpan_of_ne hx

end CFSG.StandardType

end
