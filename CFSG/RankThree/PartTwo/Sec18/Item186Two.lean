module

public import CFSG.RankThree.PartTwo.Sec18.Statements
public import CFSG.RankThree.PartTwo.Sec18.Item183OneProofRemTools
import CFSG.RankThree.PartTwo.KFacts.L34Sections
import CFSG.RankThree.PartTwo.KFacts.KS14SL34
import CFSG.RankThree.PartTwo.Sec18.SylowPlane
import CFSG.RankThree.PartTwo.Sec18.Item186a
import CFSG.RankThree.PartTwo.Sec18.Item186Act
import CFSG.RankThree.PartTwo.Sec18.Item186Three
import CFSG.RankThree.PartTwo.Sec5.Items52
import CFSG.RankThree.PartTwo.Sec6.Item612Basic
import CFSG.LieType.BorelTits.Basic
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
import CFSG.RankThree.PartTwo.KFacts.KS12MovesSL
import CFSG.RankThree.PartTwo.Sec4.Census.Interface
import CFSG.RankThree.PartTwo.Sec4.Census.Interface46
import CFSG.RankThree.PartTwo.Sec4.LThreePiSLOn
import CFSG.RankThree.PartTwo.Sec6.Statements
import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

namespace Item186Proof

variable {G : Type} [Group G] [Finite G] {A M H : Subgroup G} {c : G}

theorem le_normalizer_pCoreOf_inf (h : Sec18Std G A M) (hH : H ∈ scriptH A M) :
    A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (H ⊓ M) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (le_inf (le_of_mem_scriptH₀ (mem_scriptH_iff_mem_scriptH₀.mp hH).1) (sec18Std_le h)).trans
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (H ⊓ M))

section Certified

theorem le_of_le_normalizer (h1812 : Item181_2) (h184 : Item184_1) (hH : Sec18H G A M H c)
    (hHs : H ∈ scriptHStar A M) {U : Subgroup G} (hU2 : IsPGroup 2 U)
    (hAU : A ≤ Subgroup.normalizer (U : Set G)) (hSU : CFSG.Open.pCoreOf 2 (H ⊓ M) ≤ U)
    (hUN : U ≤ Subgroup.normalizer (inSubgroup perfectResidual H : Set G)) :
    U ≤ CFSG.Open.pCoreOf 2 (H ⊓ M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hH.toSec18Std
  set L := inSubgroup perfectResidual H with hLdef
  set S := CFSG.Open.pCoreOf 2 (H ⊓ M) with hSdef
  set D := Sec4.thetaQuotCentralizer L with hDdef
  have hH₀ := (mem_scriptH_iff_mem_scriptH₀.mp hH.mem_scriptH).1
  have hAH : A ≤ H := le_of_mem_scriptH₀ hH₀
  have hO2le : CFSG.Open.pCoreOf 2 H ≤ S := pCoreOf_le_pCoreOf_inf h hAH
  have hSH : S ≤ H := (CFSG.LieType.BorelTits.pCoreOf_le 2 (H ⊓ M)).trans inf_le_left
  have hHNL : H ≤ Subgroup.normalizer (L : Set G) := le_normalizer_inSubgroup_perfectResidual H
  have hNLD : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (D : Set G) :=
    Sec6.normalizer_le_normalizer_thetaQuotCentralizer L
  obtain ⟨eL⟩ := (h184 G A M h H hH.mem_scriptH).1
  have hLp : ⁅L, L⁆ = L := commutator_inSubgroup_perfectResidual H
  set U₀ := U ⊓ D with hU₀
  have hLU₀ : L ≤ Subgroup.normalizer (U₀ : Set G) := by
    intro l hl
    refine mem_normalizer_of_map_conj_le ?_
    rintro _ ⟨u, ⟨huU, huD⟩, rfl⟩
    have hluD : l * u * l⁻¹ ∈ D :=
      (Subgroup.mem_normalizer_iff.mp (hNLD (Subgroup.le_normalizer hl)) u).mp huD
    have huN : u ∈ Subgroup.normalizer (L : Set G) := (Sec6.mem_thetaQuotCentralizer_iff.mp huD).1
    have hcL : l * u * l⁻¹ * u⁻¹ ∈ L := by
      have h1 : u * l⁻¹ * u⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp huN _).mp (L.inv_mem hl)
      have e : l * u * l⁻¹ * u⁻¹ = l * (u * l⁻¹ * u⁻¹) := by group
      rw [e]
      exact L.mul_mem hl h1
    have hcU : l * u * l⁻¹ * u⁻¹ ∈ U :=
      hSU (hO2le (pCoreOf_le_pCoreOf_of_mem_oTwoComponentsIn hH₀.2.1
        (inf_thetaQuotCentralizer_le hLp eL ⟨hcL, D.mul_mem hluD (D.inv_mem huD)⟩)))
    refine ⟨?_, hluD⟩
    show l * u * l⁻¹ ∈ U
    have h1 := U.mul_mem hcU huU
    rwa [inv_mul_cancel_right] at h1
  have hAU₀ : A ≤ Subgroup.normalizer (U₀ : Set G) := fun a ha =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hAU ha, hNLD (hHNL (hAH ha))⟩
  have hSU₀ : S ≤ Subgroup.normalizer (U₀ : Set G) := fun s hs =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer (hSU hs), hNLD (hHNL (hSH hs))⟩
  have hHU₀ : H ≤ Subgroup.normalizer (U₀ : Set G) :=
    hH₀.1.le.trans (sup_le (sup_le hLU₀ hAU₀) hSU₀)
  have hU₀O : U₀ ≤ CFSG.Open.pCoreOf 2 H :=
    le_pCoreOf_of_mem_scriptHStar h hHs (hU2.to_le inf_le_left) hHU₀
  obtain ⟨s, hsS, hsO⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hO2le hH₀.2.2)
  have hsD : s ∉ D := fun hsD => hsO (hU₀O ⟨hSU hsS, hsD⟩)
  have hA := isE27_of_mem_partTwoE h.mem_partTwoE
  have hB9 : Nat.card (A ⊓ L : Subgroup G) = 9 := card_inf_of_sec18H h1812 h184 hH
  have hB3 : IsPGroup 3 (A ⊓ L : Subgroup G) := fun x =>
    ⟨1, Subtype.ext (by simpa using hA.1.2 _ x.2.1)⟩
  intro u hu
  by_cases huD : u ∈ D
  · exact hO2le (hU₀O ⟨hu, huD⟩)
  · have hsu := inv_mul_mem_thetaQuotCentralizer hLp eL inf_le_right hB9 hB3 hU2 hUN
      (inf_le_left.trans hAU) (hSU hsS) hu hsD huD
    have h1 : s⁻¹ * u ∈ S := hO2le (hU₀O ⟨U.mul_mem (U.inv_mem (hSU hsS)) hu, hsu⟩)
    have h2 := S.mul_mem hsS h1
    rwa [mul_inv_cancel_left] at h2

end Certified

end Item186Proof

end CFSG.RankThree.PartTwo.Sec18
