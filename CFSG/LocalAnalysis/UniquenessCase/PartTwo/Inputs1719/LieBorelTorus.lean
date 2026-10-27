module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OuterCyclic
public import CFSG.LocalAnalysis.UniquenessCase.UCFront11
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Blueprint.LieModelAPI
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.Quasithin.Background.QuasisimpleSp4G2Facts
public import CFSG.Quasithin.Vol2.Ch5Sec3Statements
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsU4
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsG2
public import CFSG.ClassicalInvolution.SmallCases.NobqU3
public import CFSG.ClassicalGroups.UnitaryFlag.ModelTransport
public import CFSG.LieType.Chevalley.AdjointCenter
public import TauCeti.Algebra.Group.NormalizerQuotient.Basic
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
public import CFSG.GH74.BNPair.Defs
public import CFSG.GH74.GLS.IVK.L2.F1
public import CFSG.GH74.KGroups.L3EpsNoNormalThree
public import CFSG.GH74.KGroups.L3EpsOutExp
public import CFSG.GH74.KGroups.L3EpsOuterLin
public import CFSG.LieType.Multipliers.U62Sylow
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
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Bounded
public import CFSG.LocalAnalysis.SectionRank.QTK.EvenOrth
public import CFSG.LocalAnalysis.SectionRank.QTK.Exc
public import CFSG.LocalAnalysis.SectionRank.QTK.OddOrth
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20b
public import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E6TorusFacts
public import CFSG.Quasithin.Vol2.Ch4Sec3L436
public import CFSG.Quasithin.Vol2.Ch7Sec77Inputs
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
public import CFSG.Sporadic.Recognition.JankoWongPSLNine
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.QuasithinUnique (IsSylowTwoOf)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open TauCeti.Subgroup (normalizerQuotient)

@[expose] def K_U4CartanRank : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (n : ℕ), LieModel Y .PSU 4 2 n → 2 < 2 ^ n →
    ∀ S : Subgroup Y, IsSylowTwoOf S ⊤ →
      ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ 2 ^ n - 1 →
        pRank r (⊤ : Subgroup (normalizerQuotient S)) = 2 ∧
          Nat.card (CFSG.LocalAnalysis.UniquenessCase.UC22.F11.Omega1p r
            (⊤ : Subgroup (normalizerQuotient S))) = r ^ 2 ∧
            (Nat.card Y).factorization r = (Nat.card (normalizerQuotient S)).factorization r

@[expose] def K_Sp4CartanRank : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (n : ℕ), LieModel Y .PSp 2 2 n → 2 < 2 ^ n →
    ∀ S : Subgroup Y, IsSylowTwoOf S ⊤ →
      IsMulCommutative (normalizerQuotient S) ∧
        ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ 2 ^ n - 1 →
          pRank r (⊤ : Subgroup (normalizerQuotient S)) = 2 ∧
            Nat.card (CFSG.LocalAnalysis.UniquenessCase.UC22.F11.Omega1p r
              (⊤ : Subgroup (normalizerQuotient S))) = r ^ 2 ∧
              (Nat.card Y).factorization r = (Nat.card (normalizerQuotient S)).factorization r

@[expose] def K_G2CartanRank : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (n : ℕ), LieModel Y .G2 0 2 n → 2 < 2 ^ n →
    ∀ S : Subgroup Y, IsSylowTwoOf S ⊤ →
      ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ 2 ^ n - 1 →
        pRank r (⊤ : Subgroup (normalizerQuotient S)) = 2 ∧
          Nat.card (CFSG.LocalAnalysis.UniquenessCase.UC22.F11.Omega1p r
            (⊤ : Subgroup (normalizerQuotient S))) = r ^ 2 ∧
            (r ≠ 3 →
              (Nat.card Y).factorization r = (Nat.card (normalizerQuotient S)).factorization r)

@[expose] def K_LieBorelTorus : Prop :=
  (∀ (Y : Type) [Group Y] [Finite Y] (n : ℕ), LieModel Y .PSU 4 2 n → 2 < 2 ^ n →
    ∀ S : Subgroup Y, IsSylowTwoOf S ⊤ →
      IsMulCommutative (normalizerQuotient S) ∧
        ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ 2 ^ n - 1 →
          pRank r (⊤ : Subgroup (normalizerQuotient S)) = 2 ∧
            Nat.card (CFSG.LocalAnalysis.UniquenessCase.UC22.F11.Omega1p r
              (⊤ : Subgroup (normalizerQuotient S))) = r ^ 2 ∧
              (Nat.card Y).factorization r = (Nat.card (normalizerQuotient S)).factorization r) ∧
  (∀ (Y : Type) [Group Y] [Finite Y] (n : ℕ), LieModel Y .PSp 2 2 n → 2 < 2 ^ n →
    ∀ S : Subgroup Y, IsSylowTwoOf S ⊤ →
      IsMulCommutative (normalizerQuotient S) ∧
        ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ 2 ^ n - 1 →
          pRank r (⊤ : Subgroup (normalizerQuotient S)) = 2 ∧
            Nat.card (CFSG.LocalAnalysis.UniquenessCase.UC22.F11.Omega1p r
              (⊤ : Subgroup (normalizerQuotient S))) = r ^ 2 ∧
              (Nat.card Y).factorization r = (Nat.card (normalizerQuotient S)).factorization r) ∧
  (∀ (Y : Type) [Group Y] [Finite Y] (n : ℕ), LieModel Y .G2 0 2 n → 2 < 2 ^ n →
    ∀ S : Subgroup Y, IsSylowTwoOf S ⊤ →
      IsMulCommutative (normalizerQuotient S) ∧
        ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ 2 ^ n - 1 →
          pRank r (⊤ : Subgroup (normalizerQuotient S)) = 2 ∧
            Nat.card (CFSG.LocalAnalysis.UniquenessCase.UC22.F11.Omega1p r
              (⊤ : Subgroup (normalizerQuotient S))) = r ^ 2 ∧
              (r ≠ 3 →
                (Nat.card Y).factorization r = (Nat.card (normalizerQuotient S)).factorization r))

theorem isMulCommutative_normalizerQuotient_u4 {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (hq : 2 < 2 ^ n) (hY : LieModel Y .PSU 4 2 n)
    (S : Subgroup Y) (hS : IsSylowTwoOf S ⊤) :
    IsMulCommutative (normalizerQuotient S) := by
  have hn : 2 ≤ n := by
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp at hq
    · exact h
  obtain ⟨H, F, D⟩ := CFSG.Quasithin.H13.Sec53F.lieBorelFacts_u4 Y n
    ⟨hn, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))⟩ hY S hS
  exact IsMulCommutative.mk (Std.Commutative.mk D.quot_comm)

theorem isMulCommutative_normalizerQuotient_g2
    {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (hq : 2 < 2 ^ n) (hY : LieModel Y .G2 0 2 n)
    (S : Subgroup Y) (hS : IsSylowTwoOf S ⊤) :
    IsMulCommutative (normalizerQuotient S) := by
  have hn : 2 ≤ n := by
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp at hq
    · exact h
  obtain ⟨H, F, D⟩ := CFSG.Quasithin.H13.Sec53F.G2.lieBorelFacts_g2 Y n
    ⟨hn, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩ hY S hS
  exact IsMulCommutative.mk (Std.Commutative.mk D.quot_comm)

theorem K_LieBorelTorus_of_parts
    (hU : K_U4CartanRank) (hSp : K_Sp4CartanRank) (hG : K_G2CartanRank) :
    K_LieBorelTorus := by
  refine ⟨?_, ?_, ?_⟩
  · intro Y _ _ n hY hq S hS
    refine ⟨isMulCommutative_normalizerQuotient_u4 hq hY S hS, fun r hr hr2 hdvd => ?_⟩
    exact hU Y n hY hq S hS r hr hr2 hdvd
  · intro Y _ _ n hY hq S hS
    exact hSp Y n hY hq S hS
  · intro Y _ _ n hY hq S hS
    refine ⟨isMulCommutative_normalizerQuotient_g2 hq hY S hS, fun r hr hr2 hdvd => ?_⟩
    exact hG Y n hY hq S hS r hr hr2 hdvd

theorem K_LieOuterCyclic_holds :
    (∀ (Y : Type) [Group Y] (n : ℕ), LieModel Y .PSU 4 2 n → IsCyclic (Outer Y)) ∧
      (∀ (Y : Type) [Group Y] (n : ℕ), LieModel Y .PSp 2 2 n → IsCyclic (Outer Y)) ∧
        (∀ (Y : Type) [Group Y] (n : ℕ), LieModel Y .G2 0 2 n → IsCyclic (Outer Y)) :=
  ⟨fun _ _ _ h => isCyclic_outer_of_lieModel_PSU4 h,
    fun _ _ _ h => isCyclic_outer_of_lieModel_PSp4 h,
    fun _ _ _ h => isCyclic_outer_of_lieModel_G2 h⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
