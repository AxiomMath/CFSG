module

public import CFSG.LocalAnalysis.StandardType.GGOmegaPlusRootGenDefs
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2FieldDataWeyl
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
open Multiplicative

variable {K : Type} [Field K] {m p : ℕ} {ζ : Kˣ}

theorem omPlusTorusGL_injective [NeZero p] (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p) :
    Function.Injective (omPlusTorusGL (K := K) (m := m) hζ) := by
  intro f g hfg
  funext i
  have h := congrArg (fun w : GL (Fin m ⊕ Fin m) K =>
    (w : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) (Sum.inl i) (Sum.inl i)) hfg
  simp only [omPlusTorusGL_apply, OmegaPilot.diagOmega_coe, Matrix.diagonal_apply_eq,
    SymplecticPilot.diagSpEntry_inl] at h
  have h1 : TableBSymp.zmodPowHom hζ (f i) = TableBSymp.zmodPowHom hζ (g i) := Units.ext h
  have h2 : TableBSymp.zmodPowHom hζ (f i * (g i)⁻¹) = 1 := by
    rw [map_mul, map_inv, h1, mul_inv_cancel]
  have h3 := (TableBSymp.zmodPowHom_eq_one_iff hζ hζo).mp h2
  exact mul_inv_eq_one.mp h3

private theorem omPlusRefl_true_apply {i j : Fin m} (hij : i < j)
    (f : Fin m → Multiplicative (ZMod p)) (k : Fin m) :
    (omPlusRefl p (⟨(i, j), hij⟩, true) f) k =
      if k = i then (f j)⁻¹ else if k = j then (f i)⁻¹ else f k := by
  rw [omPlusRefl_true (p := p) (i := i) (j := j) hij, MulAut.mul_apply, MulAut.mul_apply,
    SpCoord.sgnAut_apply, SpCoord.sgnAut_apply, SpCoord.permAut_apply, Function.comp_apply,
    Equiv.swap_inv]
  by_cases hki : k = i
  · rw [hki]
    simp [Function.update_self, Function.update_of_ne (ne_of_lt hij), Equiv.swap_apply_left]
  · rw [Function.update_of_ne hki]
    by_cases hkj : k = j
    · rw [hkj]
      simp [Function.update_self, Function.comp_apply, Equiv.swap_apply_right, hki,
        ne_of_lt hij, (ne_of_lt hij).symm]
    · simp [Function.update_of_ne hkj, Function.comp_apply,
        Equiv.swap_apply_of_ne_of_ne hki hkj, hki, hkj]

private theorem omPlusRefl_true_conj_apply {i j : Fin m} (hij : i < j)
    (f : Fin m → Multiplicative (ZMod p)) (k : Fin m) :
    ((SpCoord.sgnAut (p := p) j * SpCoord.permAut (p := p) (Equiv.swap i j) *
      SpCoord.sgnAut (p := p) j : MulAut (Fin m → Multiplicative (ZMod p))) f) k =
      if k = i then (f j)⁻¹ else if k = j then (f i)⁻¹ else f k := by
  rw [MulAut.mul_apply, MulAut.mul_apply, SpCoord.sgnAut_apply, SpCoord.sgnAut_apply,
    SpCoord.permAut_apply, Function.comp_apply, Equiv.swap_inv, Function.update_apply]
  by_cases hkj : k = j
  · rw [hkj]
    simp [Function.update_self, Function.comp_apply, Equiv.swap_apply_right,
      ne_of_lt hij, (ne_of_lt hij).symm]
  · rw [if_neg hkj]
    by_cases hki : k = i
    · rw [hki]
      simp [Function.update_self, Function.comp_apply, Equiv.swap_apply_left, hkj]
    · simp [Function.update_of_ne hkj, Function.comp_apply,
        Equiv.swap_apply_of_ne_of_ne hki hkj, hki, hkj]

private theorem omPlusRefl_mulSingle_apply {i j : Fin m} (hij : i < j) (s : Bool)
    (k : Fin m) (c : Multiplicative (ZMod p)) :
    omPlusRefl p (⟨(i, j), hij⟩, s) (Pi.mulSingle k c) =
      if k = i then Pi.mulSingle j (cond s c⁻¹ c)
      else if k = j then Pi.mulSingle i (cond s c⁻¹ c)
      else Pi.mulSingle k c := by
  cases s
  · rw [omPlusRefl_false (p := p) (i := i) (j := j) hij, SpCoord.permAut_mulSingle]
    by_cases hki : k = i
    · rw [hki]
      simp [Equiv.swap_apply_left, Bool.cond_false]
    · by_cases hkj : k = j
      · rw [hkj]
        simp [Equiv.swap_apply_right, hki, ne_of_lt hij, (ne_of_lt hij).symm,
          Bool.cond_false]
      · simp [Equiv.swap_apply_of_ne_of_ne hki hkj, hki, hkj]
  · rw [omPlusRefl_true (p := p) (i := i) (j := j) hij, MulAut.mul_apply, MulAut.mul_apply,
      SpCoord.permAut_mulSingle]
    by_cases hki : k = i
    · rw [hki]
      simp [Equiv.swap_apply_left, SpCoord.sgnAut_mulSingle_self, SpCoord.sgnAut_mulSingle_of_ne,
        ne_of_lt hij, (ne_of_lt hij).symm, Pi.mulSingle_inv, Bool.cond_true]
    · by_cases hkj : k = j
      · rw [hkj]
        simp [Equiv.swap_apply_right, SpCoord.sgnAut_mulSingle_self,
          SpCoord.sgnAut_mulSingle_of_ne, ne_of_lt hij, (ne_of_lt hij).symm, Pi.mulSingle_inv,
          Bool.cond_true]
      · simp [Equiv.swap_apply_of_ne_of_ne hki hkj, SpCoord.sgnAut_mulSingle_of_ne, hki, hkj,
          Ne.symm hki, Ne.symm hkj, Pi.mulSingle_inv]

theorem exists_mem_omPlusBlock_conj [CharP K 2] (hζ : ζ ^ p = 1) (x : OmPlusIdx m) :
    ∃ w ∈ omPlusBlock K x, ∀ f : Fin m → Multiplicative (ZMod p),
      w * omPlusTorusGL hζ f * w⁻¹ = omPlusTorusGL hζ (omPlusRefl p x f) := by
  obtain ⟨⟨⟨i, j⟩, hij⟩, s⟩ := x
  cases s
  · refine ⟨((SymplecticPilot.permSp K (Equiv.swap i j) : StatedSp m K) :
      GL (Fin m ⊕ Fin m) K), ?_, fun f => ?_⟩
    · rw [omPlusBlock_false (K := K) (i := i) (j := j) hij]
      exact OmegaPilot.permSp_swap_mem_siegelBlockGL (F := K) i j
    · rw [omPlusRefl_false (p := p) (i := i) (j := j) hij, omPlusTorusGL_apply,
        omPlusTorusGL_apply, OmegaPilot.permSp_swap_mul_diagOmega_mul_inv]
      congr 1
  · refine ⟨OmegaPilot.flipGL K {j} *
      ((SymplecticPilot.permSp K (Equiv.swap i j) : StatedSp m K) :
        GL (Fin m ⊕ Fin m) K) * (OmegaPilot.flipGL K {j})⁻¹, ?_, fun f => ?_⟩
    · rw [omPlusBlock_true (K := K) (i := i) (j := j) hij]
      exact Subgroup.mem_map_of_mem ((MulAut.conj (OmegaPilot.flipGL K {j})).toMonoidHom)
        (OmegaPilot.permSp_swap_mem_siegelBlockGL (F := K) i j)
    · rw [omPlusRefl_true (p := p) (i := i) (j := j) hij, omPlusTorusGL_apply,
        omPlusTorusGL_apply]
      set F : GL (Fin m ⊕ Fin m) K := OmegaPilot.flipGL K {j} with hF
      set P : GL (Fin m ⊕ Fin m) K :=
        ((SymplecticPilot.permSp K (Equiv.swap i j) : StatedSp m K) :
          GL (Fin m ⊕ Fin m) K) with hP
      set D : GL (Fin m ⊕ Fin m) K :=
        OmegaPilot.diagOmega K m fun k => TableBSymp.zmodPowHom hζ (f k) with hD
      have hD1 : F⁻¹ * D * F = OmegaPilot.diagOmega K m
          (OmegaPilot.flipParam K {j} fun k => TableBSymp.zmodPowHom hζ (f k)) := by
        have h := OmegaPilot.flipGL_mul_diagOmega_mul_inv (F := K) (P := {j})
          (fun k => TableBSymp.zmodPowHom hζ (f k))
        simpa only [hF, hD, OmegaPilot.flipGL_inv] using h
      have hD2 : P * OmegaPilot.diagOmega K m
            (OmegaPilot.flipParam K {j} fun k => TableBSymp.zmodPowHom hζ (f k)) * P⁻¹ =
          OmegaPilot.diagOmega K m
            ((OmegaPilot.flipParam K {j} fun k => TableBSymp.zmodPowHom hζ (f k)) ∘
              ⇑(Equiv.swap i j)) := by
        have h := OmegaPilot.permSp_swap_mul_diagOmega_mul_inv (F := K) i j
          (OmegaPilot.flipParam K {j} fun k => TableBSymp.zmodPowHom hζ (f k))
        simpa only [hP] using h
      have hD3 : F * OmegaPilot.diagOmega K m
            ((OmegaPilot.flipParam K {j} fun k => TableBSymp.zmodPowHom hζ (f k)) ∘
              ⇑(Equiv.swap i j)) * F⁻¹ =
          OmegaPilot.diagOmega K m
            (fun k => TableBSymp.zmodPowHom hζ
              ((SpCoord.sgnAut (p := p) i * SpCoord.sgnAut (p := p) j *
                SpCoord.permAut (p := p) (Equiv.swap i j) :
                MulAut (Fin m → Multiplicative (ZMod p))) f k)) := by
        rw [hF, OmegaPilot.flipGL_mul_diagOmega_mul_inv]
        congr 1
        funext k
        rw [← omPlusRefl_true (p := p) (i := i) (j := j) hij,
          omPlusRefl_true_apply (i := i) (j := j) hij]
        simp only [OmegaPilot.flipParam_apply, Function.comp_apply, Finset.mem_singleton]
        by_cases hki : k = i
        · rw [hki]
          simp [Equiv.swap_apply_left, ne_of_lt hij, (ne_of_lt hij).symm, map_inv]
        · by_cases hkj : k = j
          · rw [hkj]
            simp [Equiv.swap_apply_right, hki, ne_of_lt hij, (ne_of_lt hij).symm, map_inv]
          · simp [Equiv.swap_apply_of_ne_of_ne hki hkj, hki, hkj, map_inv]
      calc (F * P * F⁻¹) * D * (F * P * F⁻¹)⁻¹
          = F * P * (F⁻¹ * D * F) * P⁻¹ * F⁻¹ := by group
        _ = F * P * OmegaPilot.diagOmega K m
              (OmegaPilot.flipParam K {j} fun k => TableBSymp.zmodPowHom hζ (f k)) *
              P⁻¹ * F⁻¹ := by rw [hD1]
        _ = F * (P * OmegaPilot.diagOmega K m
              (OmegaPilot.flipParam K {j} fun k => TableBSymp.zmodPowHom hζ (f k)) *
              P⁻¹) * F⁻¹ := by group
        _ = F * OmegaPilot.diagOmega K m
              ((OmegaPilot.flipParam K {j} fun k => TableBSymp.zmodPowHom hζ (f k)) ∘
                ⇑(Equiv.swap i j)) * F⁻¹ := by rw [hD2]
        _ = OmegaPilot.diagOmega K m
              (fun k => TableBSymp.zmodPowHom hζ
                ((SpCoord.sgnAut (p := p) i * SpCoord.sgnAut (p := p) j *
                  SpCoord.permAut (p := p) (Equiv.swap i j) :
                  MulAut (Fin m → Multiplicative (ZMod p))) f k)) := hD3

theorem omPlusRefl_true_eq_conj {i j : Fin m} (hij : i < j) :
    omPlusRefl p (⟨(i, j), hij⟩, true) =
      SpCoord.sgnAut j * SpCoord.permAut (Equiv.swap i j) * SpCoord.sgnAut j := by
  refine MulEquiv.ext fun f => funext fun k => ?_
  rw [omPlusRefl_true_apply (i := i) (j := j) hij,
    omPlusRefl_true_conj_apply (i := i) (j := j) hij]

theorem omPlusRefl_mul_self (x : OmPlusIdx m) :
    omPlusRefl p x * omPlusRefl p x = 1 := by
  obtain ⟨⟨⟨i, j⟩, hij⟩, s⟩ := x
  cases s
  · rw [omPlusRefl_false (p := p) (i := i) (j := j) hij, ← sq]
    exact SpCoord.permAut_swap_sq i j
  · rw [omPlusRefl_true_eq_conj (i := i) (j := j) hij]
    have hsj : (SpCoord.sgnAut (p := p) j : MulAut
        (Fin m → Multiplicative (ZMod p))) * SpCoord.sgnAut (p := p) j = 1 := by
      rw [← sq]
      exact SpCoord.sgnAut_sq j
    have hpj : (SpCoord.permAut (p := p) (Equiv.swap i j) :
        MulAut (Fin m → Multiplicative (ZMod p))) *
        SpCoord.permAut (p := p) (Equiv.swap i j) = 1 := by
      rw [← sq]
      exact SpCoord.permAut_swap_sq i j
    calc (SpCoord.sgnAut j * SpCoord.permAut (Equiv.swap i j) * SpCoord.sgnAut j) *
          (SpCoord.sgnAut j * SpCoord.permAut (Equiv.swap i j) * SpCoord.sgnAut j)
        = SpCoord.sgnAut j * SpCoord.permAut (Equiv.swap i j) *
            (SpCoord.sgnAut j * SpCoord.sgnAut j) *
            SpCoord.permAut (Equiv.swap i j) * SpCoord.sgnAut j := by group
      _ = SpCoord.sgnAut j * (SpCoord.permAut (Equiv.swap i j) *
            SpCoord.permAut (Equiv.swap i j)) * SpCoord.sgnAut j := by rw [hsj]; group
      _ = SpCoord.sgnAut j * SpCoord.sgnAut j := by rw [hpj, mul_one]
      _ = 1 := hsj

theorem card_fix_omPlusRefl (hp : p.Prime) (hp2 : p ≠ 2) (x : OmPlusIdx m) :
    Nat.card {f // omPlusRefl p x f = f} * p =
      Nat.card (Fin m → Multiplicative (ZMod p)) := by
  obtain ⟨⟨⟨i, j⟩, hij⟩, s⟩ := x
  cases s
  · rw [omPlusRefl_false (p := p) (i := i) (j := j) hij]
    exact SpCoord.card_fix_permAut_swap hp hp2 (ne_of_lt hij)
  · rw [omPlusRefl_true_eq_conj (i := i) (j := j) hij]
    set s' : MulAut (Fin m → Multiplicative (ZMod p)) := SpCoord.sgnAut j with hs'
    set P : MulAut (Fin m → Multiplicative (ZMod p)) :=
      SpCoord.permAut (Equiv.swap i j) with hP
    have hss : s' * s' = 1 := by
      rw [hs', ← sq]
      exact SpCoord.sgnAut_sq j
    have hs_apply : ∀ y, s' (s' y) = y := by
      intro y
      simpa only [MulAut.mul_apply, MulAut.one_apply] using congrArg (fun φ : MulAut
        (Fin m → Multiplicative (ZMod p)) => φ y) hss
    have hfix : ∀ y, (s' * P * s') y = y ↔ P (s' y) = s' y := by
      intro y
      constructor
      · intro hy
        have h := congrArg s' hy
        simpa only [MulAut.mul_apply, hs_apply] using h
      · intro hy
        rw [MulAut.mul_apply, MulAut.mul_apply, hy, hs_apply]
    have hcard : Nat.card {y : Fin m → Multiplicative (ZMod p) // (s' * P * s') y = y} =
        Nat.card {y : Fin m → Multiplicative (ZMod p) // P y = y} :=
      Nat.card_congr (Equiv.subtypeEquiv s'.toEquiv hfix)
    calc Nat.card {y : Fin m → Multiplicative (ZMod p) // (s' * P * s') y = y} * p
        = Nat.card {y : Fin m → Multiplicative (ZMod p) // P y = y} * p := by rw [hcard]
      _ = Nat.card (Fin m → Multiplicative (ZMod p)) :=
            SpCoord.card_fix_permAut_swap hp hp2 (ne_of_lt hij)

private theorem mulSingle_cond_eq {s s' : Bool} {a b : Fin m}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (h : (Pi.mulSingle a (cond s (ofAdd (1 : ZMod p))⁻¹ (ofAdd (1 : ZMod p))) :
        Fin m → Multiplicative (ZMod p)) =
      Pi.mulSingle b (cond s' (ofAdd (1 : ZMod p))⁻¹ (ofAdd (1 : ZMod p)))) :
    a = b ∧ s = s' := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Fact (2 < p) := ⟨by have := hp.two_le; omega⟩
  have hone : (1 : ZMod p) ≠ 0 := one_ne_zero
  have hneg : (-1 : ZMod p) ≠ 0 := neg_ne_zero.mpr hone
  cases s <;> cases s' <;> simp only [Bool.cond_false, Bool.cond_true] at h
  · exact ⟨(SpCoord.mulSingle_ofAdd_eq_iff hone h).1, rfl⟩
  · rw [← ofAdd_neg] at h
    obtain ⟨-, h1⟩ := SpCoord.mulSingle_ofAdd_eq_iff hone h
    exact absurd h1.symm ZMod.neg_one_ne_one
  · rw [← ofAdd_neg] at h
    obtain ⟨-, h1⟩ := SpCoord.mulSingle_ofAdd_eq_iff hneg h
    exact absurd h1 ZMod.neg_one_ne_one
  · exact ⟨(SpCoord.mulSingle_ofAdd_eq_iff hneg h).1, rfl⟩

theorem omPlusRefl_injective (hp : p.Prime) (hp2 : p ≠ 2) :
    Function.Injective (omPlusRefl p : OmPlusIdx m → MulAut (Fin m → Multiplicative (ZMod p))) := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Fact (2 < p) := ⟨by have := hp.two_le; omega⟩
  have hg1 : (ofAdd (1 : ZMod p) : Multiplicative (ZMod p)) ≠ 1 := fun h => by
    have h1 := congrArg toAdd h
    rw [toAdd_ofAdd, toAdd_one] at h1
    exact one_ne_zero h1
  intro x x' h
  obtain ⟨⟨⟨i, j⟩, hij⟩, s⟩ := x
  obtain ⟨⟨⟨i', j'⟩, hij'⟩, s'⟩ := x'
  have hL : ∀ s : Bool, omPlusRefl p (⟨(i, j), hij⟩, s)
      (Pi.mulSingle i (ofAdd (1 : ZMod p))) =
      Pi.mulSingle j (cond s (ofAdd (1 : ZMod p))⁻¹ (ofAdd (1 : ZMod p))) := by
    intro s
    rw [omPlusRefl_mulSingle_apply (p := p) (i := i) (j := j) hij, if_pos rfl]
    rfl
  have hR : ∀ s' : Bool, omPlusRefl p (⟨(i', j'), hij'⟩, s')
      (Pi.mulSingle i (ofAdd (1 : ZMod p))) =
      (if i = i' then Pi.mulSingle j' (cond s' (ofAdd (1 : ZMod p))⁻¹ (ofAdd (1 : ZMod p)))
       else if i = j' then
         Pi.mulSingle i' (cond s' (ofAdd (1 : ZMod p))⁻¹ (ofAdd (1 : ZMod p)))
       else Pi.mulSingle i (ofAdd (1 : ZMod p))) := by
    intro s'
    rw [omPlusRefl_mulSingle_apply (p := p) (i := i') (j := j') hij']
    rfl
  have hval := congrArg (fun φ : MulAut (Fin m → Multiplicative (ZMod p)) =>
    φ (Pi.mulSingle i (ofAdd (1 : ZMod p)))) h
  rw [hL s, hR s'] at hval
  by_cases hii : i = i'
  · rw [if_pos hii] at hval
    obtain ⟨hjj, hss⟩ := mulSingle_cond_eq hp hp2 hval
    subst hii
    subst hjj
    subst hss
    exact Prod.ext (Subtype.ext rfl) rfl
  · rw [if_neg hii] at hval
    by_cases hiji : i = j'
    · rw [if_pos hiji] at hval
      obtain ⟨hji, -⟩ := mulSingle_cond_eq hp hp2 hval
      have hlt : i < j := hij
      have hlt' : i' < j' := hij'
      have h1 : i < i' := by rw [hji] at hlt; exact hlt
      have h2 : i' < i := by rw [← hiji] at hlt'; exact hlt'
      exact absurd h1 (not_lt.mpr h2.le)
    · rw [if_neg hiji] at hval
      cases s
      · simp only [Bool.cond_false] at hval
        exact absurd (SpCoord.mulSingle_ofAdd_eq_iff one_ne_zero hval).1
          (ne_of_lt hij).symm
      · simp only [Bool.cond_true] at hval
        rw [← ofAdd_neg] at hval
        exact absurd (SpCoord.mulSingle_ofAdd_eq_iff
          (neg_ne_zero.mpr (one_ne_zero : (1 : ZMod p) ≠ 0)) hval).1
          (ne_of_lt hij).symm

end CFSG.StandardType

end
