module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Quasithin.Background.A1bBasic
public import CFSG.Open.LocalVocabulary
import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213Typ
import CFSG.Quasithin.Vol2.Ch11SecE3LieSL2
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeUC.Asc1930
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
import CFSG.CGT.Timmesfeld75.L2Pair
import CFSG.CGT.Timmesfeld75.ListWCBasic
import CFSG.Certificates.Kernel.LocalCompTits.Span
import CFSG.ClassicalGroups
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingSymmetric
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Iso
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122AProved
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPrimeCompatibility
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
import CFSG.Quasithin.Background.A3Structure318Red
import CFSG.Quasithin.Background.A3Structure36A
import CFSG.Quasithin.Background.A3Structure36BBase
import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
import CFSG.Quasithin.Background.A3Structure36Base
import CFSG.Quasithin.Background.B1More13A
import CFSG.Quasithin.Background.B1More13Defs
import CFSG.Quasithin.Background.B1MoreEleven
import CFSG.Quasithin.Background.B5CompA
import CFSG.Quasithin.Background.B5CompB
import CFSG.Quasithin.Background.InternalSecB51
import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
import CFSG.Quasithin.Vol2.Ch10SecA1012Three
import CFSG.Quasithin.Vol2.Ch10SecA1012Two
import CFSG.Quasithin.Vol2.Ch10SecAShapeCard
import CFSG.Quasithin.Vol2.Ch10StatementsE
import CFSG.RankThree.Asc83Table.PermTables
import CFSG.Sporadic.Schreier.M11
import CFSG.Sporadic.Schreier.M22
import CFSG.StronglyEmbedded.ParityCriterion
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CPrime
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralAut
import CFSG.Walter.J1
import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
import Certificates.Kernel.J4Count.FixCE
import Certificates.Kernel.J4Count.FixCPairBase1
import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.Campbell340

variable {G : Type} [Group G] [Finite G]

theorem exists_sl2_quotient {H L : Subgroup G} {n : ℕ}
    (hL : L = CFSG.Quasithin.opResidual 2 H) (hL2 : IsL2 (Bar2 L) n)
    (hHL : H = L ⊔ CFSG.Open.pCoreOf 2 H) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2)
      (π : ↥H →* Matrix.SpecialLinearGroup (Fin 2) k),
      Function.Surjective π ∧ π.ker = CFSG.pCore 2 ↥H ∧ Nat.card k = 2 ^ n ∧ 2 ≤ n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSC : CFSG.Quasithin.IsPSL 2 2 n (Bar2 L) :=
    CFSG.Blueprint.LieModel.statedClassicalModel hL2 (by decide)
  obtain ⟨hn2, K, hK, hKfin, hKchar, hKcard, he2⟩ :=
    CFSG.Quasithin.Vol2.Ch11.SecE3.exists_sl2_of_isPSL22 hSC
  obtain ⟨e₂⟩ := he2
  have hLH : L ≤ H := by rw [hL]; exact CFSG.Quasithin.opResidual_le 2 H
  have hHle : H ≤ L ⊔ CFSG.Open.pCoreOf 2 H := hHL.le
  obtain ⟨e₀⟩ := CFSG.Quasithin.H13.Ch4.T4213.nonempty_modO2_equiv
    (L := H) (LH := L) hLH hHle
  let e₁ : (↥H ⧸ CFSG.pCore 2 ↥H) ≃* Bar2 L := e₀.symm
  let π : ↥H →* Matrix.SpecialLinearGroup (Fin 2) K :=
    e₂.toMonoidHom.comp (e₁.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥H)))
  have hsurj : Function.Surjective π :=
    e₂.surjective.comp (e₁.surjective.comp (QuotientGroup.mk'_surjective _))
  have hker : π.ker = CFSG.pCore 2 ↥H := by
    ext x
    rw [MonoidHom.mem_ker]
    change e₂ (e₁ (QuotientGroup.mk x)) = 1 ↔ x ∈ CFSG.pCore 2 ↥H
    rw [MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  exact ⟨K, hK, hKfin, hKchar, π, hsurj, hker, hKcard, hn2⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.Campbell340

end
