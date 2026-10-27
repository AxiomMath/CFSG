module

public import CFSG.Open.StatedDefs
import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesOrders
import CFSG.Timmesfeld.Orders.ClassicalOmega
import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.LieType.CurtisTits.SpecialLinear
import CFSG.LieType.Steinberg.Classical.SpinFrame
import CFSG.LieType.Steinberg.Families
import CFSG.LieType.Steinberg.G2
import CFSG.LieType.Universal.Spin.Generation
import CFSG.LieType.Universal.Spin.OddCT
import CFSG.LieType.Universal.Spin.PlusCT
import CFSG.LieType.Universal.Spin.Structure
import CFSG.LieType.Universal.SpinOmega
import CFSG.LieType.Universal.Unitary
import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
import CFSG.LocalAnalysis.SectionRank.SporadicCover
import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesEmbed
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotLeviFactPiece
import CFSG.Open.QuasithinDefs
import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusExtraction
import CFSG.Sporadic.M23.M23Group
import CFSG.Sporadic.Th.F2Spec
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KOrdNat

open CFSG.Open
open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

theorem card_statedOmega_quadMinus_two_eq (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nat.card ↥(StatedOmega (StatedQuadMinus 2 K b c)) = Nat.card K ^ 2 * (Nat.card K ^ 4 - 1) := by
  rw [CFSG.SeitzReduction.F4Pilot.natCard_statedOmega_quadMinus_two hirr,
    CFSG.SeitzReduction.F4Pilot.ordSL_two, ← pow_mul, show 2 * 2 = 4 from rfl]

theorem pow_three_dvd_card_statedOmega_quadMinus_three (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nat.card K ^ 3 ∣ Nat.card ↥(StatedOmega (StatedQuadMinus 3 K b c)) := by
  rw [CFSG.SeitzReduction.F4Pilot.natCard_statedOmega_quadMinus_three hirr,
    CFSG.SeitzReduction.F4Pilot.ordSU_four]
  exact dvd_mul_of_dvd_left (pow_dvd_pow _ (by norm_num)) _

theorem pow_three_dvd_card_statedOmega_quadMinus_four (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nat.card K ^ 3 ∣ Nat.card ↥(StatedOmega (StatedQuadMinus 4 K b c)) := by
  have hproj := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega_quadMinus
    (K := K) (b := b) (c := c) (n := 4) le_rfl hirr
  have hv : ∃ v, quadMinus 4 K b c v ≠ 0 := by
    let P : HypPair (quadMinus 4 K b c) := minusPair K b c (⟨0, by norm_num⟩ : Fin (4 - 1))
    exact ⟨P.e + P.f, by
      rw [CFSG.Timmesfeld.ClassicalOrders.map_add_eq_one_of_hypPair P]
      exact one_ne_zero⟩
  have hcard := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega
    (K := K) (Q := quadMinus 4 K b c) (Q₀ := StatedQuadMinus 4 K b c)
    (coe_quadMinus 4 K b c) hv
  rw [hcard] at hproj
  have hmain : ((Nat.card K ^ 3 : ℕ) : ℤ) ∣
      (Nat.card ↥(StatedOmega (StatedQuadMinus 4 K b c)) : ℤ) := by
    rw [hproj, Nat.cast_pow, mul_assoc]
    exact dvd_mul_of_dvd_left (pow_dvd_pow _ (by norm_num)) _
  exact Int.natCast_dvd_natCast.mp hmain

end CFSG.LocalAnalysis.UniquenessCase.UC22.KOrdNat

end
