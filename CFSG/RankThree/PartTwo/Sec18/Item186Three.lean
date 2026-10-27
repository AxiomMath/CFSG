module

public import CFSG.RankThree.PartTwo.Sec18.Statements
public import CFSG.RankThree.PartTwo.Sec18.Item183OneProofRemTools
import CFSG.RankThree.PartTwo.KFacts.L34Sections
import CFSG.RankThree.PartTwo.KFacts.KS14SL34
import CFSG.RankThree.PartTwo.Sec18.SylowPlane
import CFSG.RankThree.PartTwo.Sec18.Item186a
import CFSG.RankThree.PartTwo.Sec18.Item186Rank
import CFSG.CharacterTheory.Semidihedral.OddFieldLift
import CFSG.LinearAlgebra.LinearGroups.CoordinateData
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSmallSourceLinear
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModelSelector
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

namespace Item186Proof

variable {G : Type} [Group G] [Finite G] {A M H : Subgroup G} {c : G}

theorem mem_normalizer_of_map_conj_le {Y : Subgroup G} {g : G}
    (h : Y.map (MulAut.conj g).toMonoidHom ≤ Y) : g ∈ Subgroup.normalizer (Y : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge h ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem pCoreOf_inf_le {X L : Subgroup G} (hLX : L ≤ X) :
    CFSG.Open.pCoreOf 2 X ⊓ L ≤ CFSG.Open.pCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
    (fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X (hLX hx), Subgroup.le_normalizer hx⟩)
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).to_le inf_le_left)

theorem zpowers_eq_of_mem' {c z : G} (hc3 : orderOf c = 3) (hz : z ∈ Subgroup.zpowers c)
    (hz1 : z ≠ 1) : Subgroup.zpowers z = Subgroup.zpowers c := by
  have hz3 : z ^ 3 = 1 := by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hc3, pow_orderOf_eq_one,
      one_zpow]
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz) ?_
  rw [Nat.card_zpowers, Nat.card_zpowers, hc3, orderOf_eq_prime hz3 hz1]

theorem eq_one_of_commutator_mem (h184 : Item184_1) (hH : Sec18H G A M H c) {X : Subgroup G}
    (hLX : inSubgroup perfectResidual H ≤ X) {b : G} (hbA : b ∈ A)
    (hbL : b ∈ inSubgroup perfectResidual H)
    (hb : ∀ l ∈ inSubgroup perfectResidual H, b * l * b⁻¹ * l⁻¹ ∈ CFSG.Open.pCoreOf 2 X) :
    b = 1 := by
  set L := inSubgroup perfectResidual H with hLdef
  have hbc : b ∈ (Subgroup.zpowers c : Set G) := by
    rw [← hH.centralizer_eq]
    refine ⟨hbA, fun l hl => pCoreOf_inf_le hLX ⟨hb l hl, ?_⟩⟩
    exact L.mul_mem (L.mul_mem (L.mul_mem hbL hl) (L.inv_mem hbL)) (L.inv_mem hl)
  by_contra hb1
  apply not_mem_of_sec18H h184 hH
  have h1 := zpowers_eq_of_mem' (orderOf_eq_three_of_sec18H h184 hH) hbc hb1
  have hc : c ∈ Subgroup.zpowers b := h1 ▸ Subgroup.mem_zpowers c
  exact (Subgroup.zpowers_le.mpr hbL) hc

end Item186Proof

end CFSG.RankThree.PartTwo.Sec18
