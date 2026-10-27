module

public import CFSG.Quasithin.Vol2.Asc94.HeK1
public import CFSG.Quasithin.Vol2.Asc94.HeNB5
public import CFSG.Quasithin.Vol2.Asc94.TSLeafK
public import CFSG.Assembly.OddCoreSpan
public import CFSG.GH74.Generic.S45.LSporMathA
public import CFSG.Literature.GL52
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma22
public import CFSG.LocalAnalysis.ComponentClassification.AS81Reduce
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeCaseFinal
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Step49Held
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XTheorem4
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionFitting
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionMoved
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5Containment
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveComponents
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitGlaubermanCore
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFixedFactorSylowReduction
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.FittingNilpotence
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.RankThree.PartOne.KS.PKit
public import CFSG.RankThree.PartOne.KS.PKitLines
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartOne.S8.Statements

public section

namespace CFSG.Quasithin.A94

open Subgroup CFSG.CGT.Timmesfeld75 CFSG.CGT.M24S CFSG.Open CFSG.Blueprint
open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoL3Four
open CFSG.ComponentClassification.AS81

variable {G : Type} [Group G] [Finite G] {z : G}

@[expose] def HeGeometry (e : ↥(Cz z) ≃* L52.Hc) : Prop :=
  ∃ (A R : Subgroup G) (g : G),
    standardComponentIsStandard A ∧ TypeL34 (rankTwoQuot A) ∧
    R ≤ A ∧ IsSylowOf 2 R (centralizer (A : Set G)) ∧ IsElemAbelian 2 R ∧ Nat.card R = 4 ∧
    tr e L52.A1 ≤ A ∧ tr e L52.A2 ≤ A ∧ R ≤ tr e L52.A1 ∧ R ≤ tr e L52.A2 ∧
    g ∉ normalizer (A : Set G) ∧ rightConjugate R g ≤ centralizer (R : Set G) ∧
    rightConjugate R g ≤ A ∧
    tr e L52.A1 ⊓ tr e L52.A2 = R ⊔ rightConjugate R g ∧
    tr e L52.A1 ⊓ tr e L52.A2 = centerIn (tr e L52.A1 ⊔ tr e L52.A2) ∧
    IsSylowOf 2 (tr e L52.A1 ⊔ tr e L52.A2) A

@[expose] def HeGeometryStmt : Prop :=
  L52.F6Model → ∀ (G : Type) [Group G] [Finite G] (z : G) (e : ↥(Cz z) ≃* L52.Hc),
    IsSimpleGroup G → CFSG.Assembly.KProper CFSG.Blueprint.Catalog G → Setting G z e →
    Subgroup.normalizer (tr e L52.U1 : Set G) = Cz z →
    Subgroup.normalizer (tr e L52.U2 : Set G) = Cz z →
    HeGeometry e

end CFSG.Quasithin.A94
