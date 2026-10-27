module

public import CFSG.LocalAnalysis.StandardType.GGSixA6RedSpRestr
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedSpRestrStd
public import CFSG.ClassicalGroups.Symplectic.Simple
public import CFSG.ClassicalGroups.Symplectic.ComponentCartanRank
public import CFSG.LieType.Universal.Symplectic
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.Open.StatedAPI
public import CFSG.ClassicalGroups.Symplectic.DiagonalTorusRank
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Steinberg.CentralExt.SpCentrallyClosed
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.SignalizerFunctorTheorem.NonLocal.Cross
public import CFSG.SignalizerFunctorTheorem.NonLocal.SpData
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.StandardType.A6Red

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank
open LinearMap (BilinForm)

theorem ggA6_spLie {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] [Finite F] [CharP F 2] [FiniteDimensional F V] (B : BilinForm F V) (hB : B.IsAlt) (hnd : B.Nondegenerate) (U : Submodule F V)
    (hU : (B.restrict U).Nondegenerate) (m f : ℕ) (hcard : Nat.card F = 2 ^ f)
    (hdim : Module.finrank F U = 2 * m) (hm : 3 ≤ m) :
    IsSimpleGroup ↥(ggA6SpFixer B (B.orthogonal U)) ∧
      LieModel ↥(ggA6SpFixer B (B.orthogonal U)) .PSp m 2 f := by
  have hB' : (B.restrict U).IsAlt := fun x => hB x
  obtain ⟨e1, -⟩ := ggA6_sp_restr_equiv B hB hnd U hU
  obtain ⟨e2⟩ := ggA6_sp_std_equiv (V := V) (B.restrict U) hB' hU m (by omega)
  let e : ↥(ggA6SpFixer B (B.orthogonal U)) ≃* StatedSp m F := e1.trans e2
  have hf : 1 ≤ f := by
    by_contra h
    have hf0 : f = 0 := by omega
    rw [hf0, pow_zero] at hcard
    have h2 : 2 ≤ Nat.card F := by
      have := Finite.one_lt_card (α := F)
      omega
    omega
  have hne : (m, 2 ^ f) ≠ (2, 2) := by
    rintro h
    have hm2 : m = 2 := congrArg Prod.fst h
    omega
  have hadm : StatedLieAdmissible .PSp m 2 f :=
    ⟨Nat.prime_two, hf, by omega, hne⟩
  have hZ : Subgroup.center (StatedSp m F) = ⊥ :=
    CFSG.ClassicalGroups.Symplectic.center_statedSp_eq_bot_of_charP_two (m := m) (F := F) (by omega)
  have hmodel : StatedClassicalModel
      (StatedSp m F ⧸ Subgroup.center (StatedSp m F)) .PSp m 2 f :=
    CFSG.LieType.Universal.Symplectic.statedClassicalModel_center_quotient (n := m) (F := F)
      hadm hcard
  have q : StatedSp m F ≃* (StatedSp m F ⧸ Subgroup.center (StatedSp m F)) :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  have hclass : StatedClassicalModel ↥(ggA6SpFixer B (B.orthogonal U)) .PSp m 2 f :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv (e.trans q).symm hmodel
  refine ⟨?_, ?_⟩
  · exact CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp _ m 2 f hclass
  · exact Or.inl ⟨by decide, hclass⟩

theorem ggA6_spFour {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] [Finite F] [CharP F 2] [FiniteDimensional F V] (B : BilinForm F V) (hB : B.IsAlt) (hnd : B.Nondegenerate) (U : Submodule F V)
    (hU : (B.restrict U).Nondegenerate) (hcard : Nat.card F = 2) (hdim : Module.finrank F U = 4)
    {J L : Subgroup (V ≃ₗ[F] V)} (hJL : J ≤ L) (hL : IsComponentOf L (ggA6SpFixer B (B.orthogonal U)))
    (hA6 : Nonempty (↥J ≃* alternatingGroup (Fin 6))) : J = L := by
  let H : Subgroup (V ≃ₗ[F] V) := ggA6SpFixer B (B.orthogonal U)
  have hLH : L ≤ H := hL.1
  have hJH : J ≤ H := hJL.trans hLH
  have hHcard : Nat.card ↥H = 720 := by
    obtain ⟨e1, -⟩ := ggA6_sp_restr_equiv B hB hnd U hU
    obtain ⟨e2⟩ := ggA6_sp_std_equiv (V := V) (B.restrict U) (fun x => hB x) hU 2 (by omega)
    rw [Nat.card_congr (e1.trans e2).toEquiv,
      CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp_two F, hcard]
    norm_num
  have hJcard : Nat.card ↥J = 360 := by
    obtain ⟨eJ⟩ := hA6
    rw [Nat.card_congr eJ.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  have hJ'card : Nat.card ↥(J.subgroupOf H) = 360 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJH).toEquiv).trans hJcard
  have hindex : (J.subgroupOf H).index = 2 := by
    have hmul := (J.subgroupOf H).card_mul_index
    rw [hJ'card, hHcard] at hmul
    omega
  have hcommHJ : ⁅H, H⁆ ≤ J := by
    haveI : (J.subgroupOf H).Normal := Subgroup.normal_of_index_eq_two hindex
    have hquot : Nat.card (↥H ⧸ J.subgroupOf H) = 2 := by
      rw [Subgroup.index_eq_card] at hindex
      exact hindex
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : IsCyclic (↥H ⧸ J.subgroupOf H) := isCyclic_of_prime_card (p := 2) hquot
    haveI : IsMulCommutative (↥H ⧸ J.subgroupOf H) := IsCyclic.isMulCommutative
    have hcommH : commutator ↥H ≤ J.subgroupOf H :=
      (Subgroup.Normal.quotient_commutative_iff_commutator_le
        (N := J.subgroupOf H)).mp inferInstance
    rw [Subgroup.commutator_le]
    intro h₁ hh₁ h₂ hh₂
    have hmem := hcommH (Subgroup.commutator_mem_commutator
      (show (⟨h₁, hh₁⟩ : ↥H) ∈ (⊤ : Subgroup ↥H) from trivial)
      (show (⟨h₂, hh₂⟩ : ↥H) ∈ (⊤ : Subgroup ↥H) from trivial))
    rw [Subgroup.mem_subgroupOf] at hmem
    simpa [commutatorElement_def] using hmem
  haveI : Group.IsPerfect ↥L := Group.IsPerfect.mk hL.2.2.1
  have hLL : ⁅L, L⁆ = L := Subgroup.commutator_eq_self
  have hLJ : L ≤ J := by
    calc L = ⁅L, L⁆ := hLL.symm
      _ ≤ ⁅H, H⁆ := Subgroup.commutator_mono hLH hLH
      _ ≤ J := hcommHJ
  exact le_antisymm hJL hLJ

end CFSG.StandardType.A6Red
