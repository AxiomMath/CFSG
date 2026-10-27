module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21c
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.ClassicalGroups
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.GH74.GLS.IVK.L2.F1
public import CFSG.GH74.KGroups.L3EpsNoNormalThree
public import CFSG.GH74.KGroups.L3EpsOutExp
public import CFSG.GH74.KGroups.L3EpsOuterLin
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeCore
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeUnitary
public import CFSG.LieType.SeitzGeneration.UnitaryBlocks
public import CFSG.LieType.SeitzGeneration.UnitaryHyperScope
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Bounded
public import CFSG.LocalAnalysis.SectionRank.QTK.EvenOrth
public import CFSG.LocalAnalysis.SectionRank.QTK.Exc
public import CFSG.LocalAnalysis.SectionRank.QTK.OddOrth
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20b
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21b
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07
public import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
public import CFSG.Milestones.ASVolI.I2
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.OddKernel.CompleteRankComparison
public import CFSG.RankThree.PartOne.KF.ClsPSL
public import CFSG.RankThree.PartOne.KF.SU5Model
public import CFSG.RankThree.PartOne.KF.SymCtxMatrix
public import CFSG.RankThree.PartOne.KF.ToralQuot
public import CFSG.RankThree.PartOne.KF.UnitaryModel
public import CFSG.RankThree.PartOne.S11c.Sec66PSL
public import CFSG.RankThree.PartOne.S11c.Sec66Sp
public import CFSG.RankThree.PartOne.S11c.SuFiveD
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutUnitary
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open scoped Pointwise

section Section22Context

variable {G : Type} [Group G] [Finite G]

@[expose] def kerAct (M V : Subgroup G) : Subgroup ↥M :=
  (centralizer (V : Set G)).subgroupOf M

abbrev MBar (M V : Subgroup G) : Type := ↥M ⧸ (kerAct M V).normalCore

@[expose] def mbarImage (M V X : Subgroup G) : Subgroup (MBar M V) :=
  (X.subgroupOf M).map (QuotientGroup.mk' (kerAct M V).normalCore)

structure Ctx22 (D : Data G) (Ch : Choice2011 G) extends Ctx21 D Ch where
  hU : ¬ CFSG.CGT.Timmesfeld75.IsTI D.U

structure Ctx22b (D : Data G) (Ch : Choice2011 G) extends Ctx22 D Ch where
  hC : ¬ centralizer (D.Z : Set G) ≤ D.M
  L : Subgroup G
  hL : L ∈ calLOf D.T D.M (centralizer (D.Z : Set G))
  hLge : L0 ≤ L
  V : Subgroup G
  hVU : V ≤ D.U
  hVne : V ≠ ⊥
  hVM : D.M ≤ normalizer (V : Set G)
  hVirr : IrrOn D.M V

end Section22Context

section Section22a

variable {G : Type} [Group G] [Finite G]

@[expose] def S22_1 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx22 D Ch,
    D.sig3 = ∅ ∧ (D.sig2.Nonempty → D.M ⊓ centralizer (D.U : Set G) = CFSG.Open.pCoreOf 2 D.M)

@[expose] def S22_2 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx22 D Ch, ¬ centralizer (D.Z : Set G) ≤ D.M

@[expose] def S22_V (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx22b D Ch, InCalW D.M D.T c.V ∧
    ∀ p ∈ D.sig, 1 < CFSG.pRank p (MBar D.M c.V) ∧
      CFSG.Open.pRank p (D.M ⊓ centralizer (c.V : Set G)) ≤ 1

@[expose] def S22_8 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx22b D Ch, D.sig = D.sig1

@[expose] def S22_9 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx22b D Ch, ¬ MBarGT D.M ⊥ c.V (c.n + 1)

@[expose] def S22_10 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx22b D Ch, ∀ q : ℕ, q.Prime → q ≠ 2 → ∀ Q : Subgroup G,
    CFSG.ABGLocalTools.IsSylowOf q Q (barPreimage D.M (CFSG.pCore q (Bar2 D.M))) →
    1 < CFSG.Open.pRank q Q → Q ⊓ centralizer (c.V : Set G) = ⊥

@[expose] def S22_11 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx22b D Ch,
    IsCyclic ↥(CFSG.fittingSubgroup ↥(commutator (MBar D.M c.V))) ∧
      mbarImage D.M c.V c.B ≤
        Subgroup.centralizer
          (((CFSG.fittingSubgroup ↥(commutator (MBar D.M c.V))).map
            (commutator (MBar D.M c.V)).subtype : Subgroup (MBar D.M c.V)) : Set (MBar D.M c.V))

@[expose] def S22_12 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx22b D Ch, ∀ p ∈ D.sig, ∀ P : Subgroup G,
    CFSG.ABGLocalTools.IsSylowOf p P (barPreimage D.M (centE D.M)) →
      (IsCyclic ↥⁅centE D.M, centE D.M⁆ ∧
        CFSG.perfectResidual (Bar2 D.M) = CFSG.layer (Bar2 D.M) ∧
        barImage D.M P ≤ centE D.M ⊓ commutator (Bar2 D.M) ∧ (barImage D.M P).Normal ∧ IsCyclic ↥P) ∧
      ∃ g ∈ D.M, ∀ b ∈ c.B, ∀ x ∈ P.map (MulAut.conj g).toMonoidHom, b * x = x * b

@[expose] def K2213 (D : Data G) {Ch : Choice2011 G} (c : Ctx22b D Ch) (p : ℕ) (K : Subgroup G)
    (n : ℕ) : Prop :=
  K ∈ calC D.M ∧
    ((IsJ1 ↥(mbarImage D.M c.V K) ∧ n = 3 ∧ p ∣ Nat.card ↥(mbarImage D.M c.V K) ∧
        ¬ IsL2 ↥(mbarImage D.M c.V K) n) ∨
      (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)] ∨
      (IsSz ↥(mbarImage D.M c.V K) n ∧ (2 : ℤ) ^ (2 * n) ≡ -1 [ZMOD (p : ℤ)])) ∧
    ((IsSp4 ↥(mbarImage D.M c.V K) n ∧ Odd n ∧
        ∃ t : ↥D.M, (t : G) ∈ D.T ∧
          ActsNontrivOnDiagramIn (mbarImage D.M c.V K) (QuotientGroup.mk t : MBar D.M c.V)) ∨
      (IsSU3 ↥(mbarImage D.M c.V K) n ∧ n ≡ 1 [MOD 6]) ∨
      (((2 < n ∧ (IsL2 ↥(mbarImage D.M c.V K) n ∨ IsSz ↥(mbarImage D.M c.V K) n)) ∨
          (IsJ1 ↥(mbarImage D.M c.V K) ∧ n = 3)) ∧
        (conjSetOf D.M K).ncard = 2) ∨
      (Hyp2120 D { c.toCtx21 with B := c.B0, hB := c.hB0, hle := le_rfl } ∧
        (IsU3 ↥(mbarImage D.M c.V K) n ∨ IsL2 ↥(mbarImage D.M c.V K) n) ∧ IsPowTwo n))

@[expose] def S22_13 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx22b D Ch, ∀ p ∈ D.sig, ∃ (K : Subgroup G) (n : ℕ), K2213 D c p K n

@[expose] def S22_14 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx22b D Ch, ∀ p ∈ D.sig, ∀ (K : Subgroup G) (n : ℕ),
    K2213 D c p K n → c.n ≤ n

@[expose] def S22_15 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx22b D Ch, ∀ p ∈ D.sig, ∀ (K : Subgroup G) (n : ℕ),
    K2213 D c p K n → IsL2 ↥(mbarImage D.M c.V K) n

@[expose] def S22_16 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx22b D Ch, ∀ p ∈ D.sig, ∀ (K : Subgroup G) (n : ℕ),
    K2213 D c p K n → ¬ (K.subgroupOf D.M).Normal

@[expose] def S22_end (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx22b D Ch, False

end Section22a

end CFSG.LocalAnalysis.UniquenessCase.UC22
