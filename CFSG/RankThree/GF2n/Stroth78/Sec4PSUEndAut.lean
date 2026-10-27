module

public import CFSG.Fischer.Classification.Unitary.Model
public import CFSG.Open.StatedDefs
public import CFSG.RankThree.GF2n.Tim79aCitedInvol
public import Mathlib.GroupTheory.GroupAction.ConjAct

import CFSG.Fischer.Classification.Unitary.Basic
import CFSG.GH74.Exceptional.UnitaryFourTwo
import CFSG.LieType.ChevTwo.OrthogonalAutEquiv
import CFSG.Open.StatedSUFieldChange
import CFSG.Quasithin.Background.BlueprintB2Frattini
import CFSG.Timmesfeld.Orders.ClassicalOrthogonal
import Mathlib.FieldTheory.Finite.GaloisField
public import CFSG.LieType.BorelTits.CompleteFlag
import CFSG.Fischer.Uniq.CompTau
import CFSG.GH74.Generic.Certificates
import CFSG.GH74.Statements
import CFSG.GroupTheory.HallHigmanPiCore
import CFSG.LieType.Chevalley.LangRootArithmetic
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoConfig
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscape
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrHom
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrLarge
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrXGen
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbDefs
import CFSG.LocalAnalysis.AGLEmbedding.ZZPrimeDefs
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOAut
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOCoords
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOEightSwap
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOKlein
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOPlusLevi
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
import CFSG.LocalAnalysis.SectionRank.TitsCover
import CFSG.Quasithin.Background.A3Components
import CFSG.Quasithin.Background.A3ComponentsAmbient
import CFSG.Quasithin.Background.B1MoreElevenD
import CFSG.Quasithin.Background.B1MoreElevenF
import CFSG.Quasithin.Background.B1MoreNineG
import CFSG.Quasithin.Background.B4ModelsAction
import CFSG.Quasithin.Background.B4ModelsIso
import CFSG.Quasithin.Background.BlueprintB2Defs
import CFSG.Quasithin.Background.C2Basic
import CFSG.Quasithin.Background.E1
import CFSG.Quasithin.Background.E1Sec4
import CFSG.Quasithin.Background.E1Sec5
import CFSG.Quasithin.Background.E1Sec8
import CFSG.Quasithin.Background.E1Solv
import CFSG.Quasithin.Background.E1Twelve
import CFSG.Quasithin.Background.E3Cent
import CFSG.Quasithin.EmptyFaithfulMultiple.InputB19Proof
import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearBridge
import CFSG.RankThree.PartOne.S8.Statements
import CFSG.RankThree.PartTwo.Sec12.Notation
import CFSG.RankThree.PartTwo.Sec4.Census.Interface
import CFSG.RankThree.PartTwo.Sec4.Item47Statement
import CFSG.RankThree.PartTwo.Sec4.Item47Witness
import CFSG.RankThree.PartTwo.Sec8.Statements
import CFSG.Sporadic.J4.Simple
import CFSG.Sporadic.J4Base
import CFSG.Sporadic.Mathieu.M12
import CFSG.Sporadic.Mathieu.M24
import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.Fischer.Classification.Unitary

namespace Sec4PSUEnd

theorem nonempty_statedOmega_quadMinus_mulEquiv_U2 :
    Nonempty (↥(StatedOmega (StatedQuadMinus 3 (ZMod 2) 1 1)) ≃* U2 4) := by
  obtain ⟨-, K₀, _, _, hK, ⟨e⟩⟩ :=
    CFSG.LieType.ChevTwo.statedClassicalModel_statedOmega_quadMinus_three_two
  have : Fintype K₀ := Fintype.ofFinite K₀
  have : Fintype CFSG.Blueprint.Fischer.K := Fintype.ofFinite _
  have hc : Fintype.card K₀ = Fintype.card CFSG.Blueprint.Fischer.K := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      CFSG.Fischer.Classification.Unitary.card_K]
  exact ⟨(e.trans (CFSG.Open.StatedSUFieldChange.statedProjSUEquiv
    (FiniteField.ringEquivOfCardEq hc) 4 (2 ^ 1))).trans CFSG.GH74.Exceptional.u2FourEquiv.symm⟩

theorem nonempty_mulAut_mulEquiv_oMinusSixTwo {X : Type*} [Group X] (φ : X ≃* U2 4) :
    Nonempty (MulAut X ≃* OMinusSixTwo) := by
  obtain ⟨ω⟩ := nonempty_statedOmega_quadMinus_mulEquiv_U2
  obtain ⟨κ⟩ := CFSG.LieType.ChevTwo.nonempty_orthogonalGroup_quadMinus_three_two_equiv_mulAut
  exact ⟨(MulAut.congr (φ.trans ω.symm)).trans κ.symm⟩

theorem card_mulAut_of_mulEquiv_U2 {X : Type*} [Group X] (φ : X ≃* U2 4) :
    Nat.card (MulAut X) = 51840 := by
  obtain ⟨ψ⟩ := nonempty_mulAut_mulEquiv_oMinusSixTwo φ
  rw [Nat.card_congr ψ.toEquiv]
  have h : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup
      (CFSG.LieType.Universal.Spin.quadMinus 3 (ZMod 2) 1 1)) : ℤ) = _ :=
    (CFSG.Timmesfeld.ClassicalOrders.card_quadMinus (K := ZMod 2) (b := 1) (c := 1) 2
      (by decide)).2
  have h2 : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup
      (CFSG.LieType.Universal.Spin.quadMinus 3 (ZMod 2) 1 1)) : ℤ) = ((51840 : ℕ) : ℤ) := by
    rw [h, Nat.card_zmod]
    decide
  exact_mod_cast h2

theorem bijective_conjNormal_comp_subtype {Y : Type*} [Group Y] [Finite Y] {X : Subgroup Y}
    [X.Normal] (φ : ↥X ≃* U2 4) {K : Subgroup Y} (hXK : X ≤ K) (hne : X ≠ K)
    (hKC : K ⊓ Subgroup.centralizer (X : Set Y) = ⊥) :
    Function.Bijective ((MulAut.conjNormal (H := X)).comp K.subtype) := by
  have hA : Nat.card (MulAut ↥X) = 51840 := card_mulAut_of_mulEquiv_U2 φ
  have : Finite (MulAut ↥X) := Nat.finite_of_card_ne_zero (by rw [hA]; norm_num)
  have hinj : Function.Injective ((MulAut.conjNormal (H := X)).comp K.subtype) := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have hk' : (k : Y) ∈ K ⊓ Subgroup.centralizer (X : Set Y) :=
      ⟨k.2, CFSG.Quasithin.BlueprintB2.mem_centralizer_of_conjNormal_eq_one hk⟩
    rw [hKC, Subgroup.mem_bot] at hk'
    exact Subtype.ext hk'
  refine hinj.bijective_of_nat_card_le ?_
  have hX : Nat.card X = 25920 :=
    (Nat.card_congr φ.toEquiv).trans CFSG.GH74.Exceptional.card_U2_four
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hXK
  have hm1 : m ≠ 1 := by
    rintro rfl
    exact hne (Subgroup.eq_of_le_of_card_ge hXK (by rw [hm, mul_one]))
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hm
    exact (Nat.card_pos (α := K)).ne' hm
  rw [hA, hm, hX]
  omega

theorem nonempty_mulEquiv_oMinusSixTwo_of_inf_centralizer_eq_bot {Y : Type*} [Group Y]
    [Finite Y] {X : Subgroup Y} [X.Normal] (φ : ↥X ≃* U2 4) {K : Subgroup Y} (hXK : X ≤ K)
    (hne : X ≠ K) (hKC : K ⊓ Subgroup.centralizer (X : Set Y) = ⊥) :
    Nonempty (↥K ≃* OMinusSixTwo) := by
  obtain ⟨ψ⟩ := nonempty_mulAut_mulEquiv_oMinusSixTwo φ
  exact ⟨(MulEquiv.ofBijective _ (bijective_conjNormal_comp_subtype φ hXK hne hKC)).trans ψ⟩

end Sec4PSUEnd

end CFSG.RankThree.GF2n.Stroth78
