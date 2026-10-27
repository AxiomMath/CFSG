module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.Open.Defs
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.Subgroup.Center
import CFSG.Timmesfeld.Orders.Classical
import CFSG.Timmesfeld.Orders.ClassicalOmega
import CFSG.Adapters.LieModelSimple
import CFSG.ClassicalGroups.Orthogonal.Simple
import CFSG.Timmesfeld.Orders.Distinct
import CFSG.RankThree.PartOne.KF.ClsOmega
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOMinusFacts
import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusPiecesOrders
import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesOrders
import CFSG.ClassicalInvolution.RouteD.TWRExoticArith
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNoTransv.Kernel
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Monster.Code.Weights
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.Background.B1Restrict
public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.EmptyFaithful.Setting
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43
import CFSG.CGT.Timmesfeld75.L2Pair
import CFSG.CGT.Timmesfeld75.ListWCBasic
import CFSG.ClassicalGroups
import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
import CFSG.LieType.Chevalley.C2E6StandardFixedData
import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
import CFSG.LieType.CurtisTits.SpecialLinear
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOAut
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOCoords
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOEightSwap
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOKlein
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOPlusLevi
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesEmbed
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCoresForms
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotLeviFactPiece
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSetup
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotLeviFactPiece
import CFSG.Quasithin.Background.G11Stmts
import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearBridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NoTransv

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo Subgroup

private theorem ordSL_two_two_pow_eq_ordA_one {m : ℕ} (hm : 1 ≤ m) :
    CFSG.SeitzReduction.F4Pilot.ordSL 2 (2 ^ m) = ordA 1 (2 ^ m) := by
  have hodd : Odd (2 ^ m - 1) :=
    CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by omega)
  rw [CFSG.SeitzReduction.F4Pilot.ordSL, ordA,
    show Nat.gcd 2 (2 ^ m - 1) = 1 from Nat.coprime_two_left.mpr hodd, Nat.div_one]

private theorem ordSU_four_two_pow_eq_ordTwistedA_three {m : ℕ} (hm : 1 ≤ m) :
    CFSG.SeitzReduction.F4Pilot.ordSU 4 (2 ^ m) = ordTwistedA 3 (2 ^ m) := by
  rw [CFSG.SeitzReduction.F4Pilot.ordSU,
    CFSG.ClassicalInvolution.RouteD.TWR.ordTwistedA_three_eq (2 ^ m)
      (Nat.one_le_pow m 2 (by norm_num))]
  have hodd : Odd (2 ^ m + 1) := by
    simpa using CFSG.Timmesfeld.Orders.odd_pow_add_one (f := m) (a := 1)
      (by omega) (by norm_num)
  rw [show Nat.gcd 4 (2 ^ m + 1) = 1 from
    Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd), Nat.div_one]
  rw [show Finset.Icc 2 4 = ({2, 3, 4} : Finset ℕ) by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  norm_num

private theorem ordSL_four_two_pow_eq_ordA_three {m : ℕ} (hm : 1 ≤ m) :
    CFSG.SeitzReduction.F4Pilot.ordSL 4 (2 ^ m) = ordA 3 (2 ^ m) := by
  have hodd : Odd (2 ^ m - 1) :=
    CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by omega)
  rw [CFSG.SeitzReduction.F4Pilot.ordSL, ordA,
    show Nat.gcd 4 (2 ^ m - 1) = 1 from
      Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd), Nat.div_one]

private theorem center_eq_bot_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : Subgroup.center H = ⊥) : Subgroup.center G = ⊥ := by
  rw [← Subgroup.map_center_eq e.symm, h, Subgroup.map_bot]

private theorem natCard_omegaMinus_four {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {k : ℕ} (hK : Nat.card K = 2 ^ k) (hk : 2 ≤ k) :
    Nat.card ↥(StatedOmega (StatedQuadMinus 2 K b c)) = ordA 1 (2 ^ (2 * k)) := by
  rw [CFSG.SeitzReduction.F4Pilot.natCard_statedOmega_quadMinus_two hirr,
    show Nat.card K ^ 2 = 2 ^ (2 * k) by rw [hK, ← pow_mul]; ring]
  exact ordSL_two_two_pow_eq_ordA_one (by omega)

private theorem natCard_omegaMinus_six {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {k : ℕ} (hK : Nat.card K = 2 ^ k) (hk : 2 ≤ k) :
    Nat.card ↥(StatedOmega (StatedQuadMinus 3 K b c)) = ordTwistedA 3 (2 ^ k) := by
  rw [CFSG.SeitzReduction.F4Pilot.natCard_statedOmega_quadMinus_three hirr, hK]
  exact ordSU_four_two_pow_eq_ordTwistedA_three (by omega)

private theorem natCard_omegaPlus_six {K : Type} [Field K] [Finite K] [CharP K 2] {k : ℕ}
    (hK : Nat.card K = 2 ^ k) (hk : 2 ≤ k) :
    Nat.card ↥(StatedOmega (StatedQuadPlus 3 K)) = ordA 3 (2 ^ k) := by
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  rw [CFSG.SeitzReduction.F4Pilot.natCard_statedOmega_quadPlus_three h4, hK]
  exact ordSL_four_two_pow_eq_ordA_three (by omega)

theorem quotient_center_of_isOmegaMinus_four {X : Type} [Group X] {k : ℕ}
    (hX : IsOmegaMinus X 4 k) (hk : 2 ≤ k) :
    IsSimpleGroup (X ⧸ center X) ∧ Nat.card (X ⧸ center X) = ordA 1 (2 ^ (2 * k)) := by
  classical
  obtain ⟨-, K, hKf, hKfin, b, c, hKcard, hirr, ⟨e⟩⟩ := hX
  letI := hKf
  letI := hKfin
  haveI hchar : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hKcard
  let Q : QuadraticForm K (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K) :=
    CFSG.LieType.Universal.Spin.quadMinus 2 K b c
  have hQ : ⇑Q = StatedQuadMinus 2 K b c := CFSG.LieType.Universal.Spin.coe_quadMinus 2 K b c
  let P := CFSG.ClassicalGroups.Orthogonal.minusPair (K := K) (b := b) (c := c) (n := 2)
    (⟨0, by norm_num⟩ : Fin (2 - 1))
  have hv : ∃ v, Q v ≠ 0 := by
    refine ⟨P.e + P.f, ?_⟩
    rw [CFSG.Timmesfeld.ClassicalOrders.map_add_eq_one_of_hypPair P]
    exact one_ne_zero
  have hbot := CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot hQ hv
  let eΩ : StatedProj (StatedOmega (StatedQuadMinus 2 K b c)) ≃*
      StatedOmega (StatedQuadMinus 2 K b c) :=
    (CFSG.RankThree.PartOne.KFU.equivProjOfScalarsBot _ hbot).symm
  let eX : X ≃* StatedOmega (StatedQuadMinus 2 K b c) := e.trans eΩ
  have hsmall :=
    CFSG.ComponentClassification.RankTwoClassical.isSimpleGroup_statedOmega_quadMinus_small
      (K := K) (b := b) (c := c) (Or.inl rfl) hirr
  have hnab : ¬ IsMulCommutative ↥(StatedOmega (StatedQuadMinus 2 K b c)) := by
    rw [isMulCommutative_iff]
    exact hsmall.2.2
  haveI hSΩ : IsSimpleGroup ↥(StatedOmega (StatedQuadMinus 2 K b c)) := hsmall.1
  have hcΩ := TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hnab
  have hcProj : Subgroup.center (StatedProj (StatedOmega (StatedQuadMinus 2 K b c))) = ⊥ :=
    center_eq_bot_of_mulEquiv eΩ hcΩ
  have hcX : Subgroup.center X = ⊥ := center_eq_bot_of_mulEquiv e hcProj
  have hSX : IsSimpleGroup X := eX.isSimpleGroup
  have hcardX : Nat.card X = ordA 1 (2 ^ (2 * k)) := by
    rw [Nat.card_congr eX.toEquiv]
    exact natCard_omegaMinus_four hirr hKcard hk
  exact quotient_center_simple_and_card hcX hcardX

theorem quotient_center_of_isOmegaMinus_six {X : Type} [Group X] {k : ℕ}
    (hX : IsOmegaMinus X 6 k) (hk : 2 ≤ k) :
    IsSimpleGroup (X ⧸ center X) ∧ Nat.card (X ⧸ center X) = ordTwistedA 3 (2 ^ k) := by
  classical
  obtain ⟨-, K, hKf, hKfin, b, c, hKcard, hirr, ⟨e⟩⟩ := hX
  letI := hKf
  letI := hKfin
  haveI hchar : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hKcard
  let Q : QuadraticForm K (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K) :=
    CFSG.LieType.Universal.Spin.quadMinus 3 K b c
  have hQ : ⇑Q = StatedQuadMinus 3 K b c := CFSG.LieType.Universal.Spin.coe_quadMinus 3 K b c
  let P := CFSG.ClassicalGroups.Orthogonal.minusPair (K := K) (b := b) (c := c) (n := 3)
    (⟨0, by norm_num⟩ : Fin (3 - 1))
  have hv : ∃ v, Q v ≠ 0 := by
    refine ⟨P.e + P.f, ?_⟩
    rw [CFSG.Timmesfeld.ClassicalOrders.map_add_eq_one_of_hypPair P]
    exact one_ne_zero
  have hbot := CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot hQ hv
  let eΩ : StatedProj (StatedOmega (StatedQuadMinus 3 K b c)) ≃*
      StatedOmega (StatedQuadMinus 3 K b c) :=
    (CFSG.RankThree.PartOne.KFU.equivProjOfScalarsBot _ hbot).symm
  let eX : X ≃* StatedOmega (StatedQuadMinus 3 K b c) := e.trans eΩ
  have hsmall :=
    CFSG.ComponentClassification.RankTwoClassical.isSimpleGroup_statedOmega_quadMinus_small
      (K := K) (b := b) (c := c) (Or.inr rfl) hirr
  have hnab : ¬ IsMulCommutative ↥(StatedOmega (StatedQuadMinus 3 K b c)) := by
    rw [isMulCommutative_iff]
    exact hsmall.2.2
  haveI hSΩ : IsSimpleGroup ↥(StatedOmega (StatedQuadMinus 3 K b c)) := hsmall.1
  have hcΩ := TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hnab
  have hcProj : Subgroup.center (StatedProj (StatedOmega (StatedQuadMinus 3 K b c))) = ⊥ :=
    center_eq_bot_of_mulEquiv eΩ hcΩ
  have hcX : Subgroup.center X = ⊥ := center_eq_bot_of_mulEquiv e hcProj
  have hSX : IsSimpleGroup X := eX.isSimpleGroup
  have hcardX : Nat.card X = ordTwistedA 3 (2 ^ k) := by
    rw [Nat.card_congr eX.toEquiv]
    exact natCard_omegaMinus_six hirr hKcard hk
  exact quotient_center_simple_and_card hcX hcardX

theorem quotient_center_of_isOmegaPlus_six {X : Type} [Group X] {k : ℕ}
    (hX : IsOmegaPlus X 6 k) (hk : 2 ≤ k) :
    IsSimpleGroup (X ⧸ center X) ∧ Nat.card (X ⧸ center X) = ordA 3 (2 ^ k) := by
  classical
  obtain ⟨-, K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hX
  letI := hKf
  letI := hKfin
  haveI hchar : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hKcard
  let Q : QuadraticForm K (Fin 3 ⊕ Fin 3 → K) := CFSG.LieType.Universal.Spin.quadPlus 3 K
  have hQ : ⇑Q = StatedQuadPlus 3 K := CFSG.LieType.Universal.Spin.coe_quadPlus 3 K
  let P := CFSG.ClassicalGroups.Orthogonal.plusPair K (⟨0, by norm_num⟩ : Fin 3)
  have hv : ∃ v, Q v ≠ 0 := by
    refine ⟨P.e + P.f, ?_⟩
    rw [CFSG.Timmesfeld.ClassicalOrders.map_add_eq_one_of_hypPair P]
    exact one_ne_zero
  have hbot := CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot hQ hv
  let eΩ : StatedProj (StatedOmega (StatedQuadPlus 3 K)) ≃*
      StatedOmega (StatedQuadPlus 3 K) :=
    (CFSG.RankThree.PartOne.KFU.equivProjOfScalarsBot _ hbot).symm
  let eX : X ≃* StatedOmega (StatedQuadPlus 3 K) := e.trans eΩ
  have hcΩ : Subgroup.center (StatedOmega (StatedQuadPlus 3 K)) = ⊥ := by
    rw [CFSG.LieType.Universal.Spin.center_statedOmega_quadPlus (n := 3) (by norm_num), hbot]
  have hcProj : Subgroup.center (StatedProj (StatedOmega (StatedQuadPlus 3 K))) = ⊥ :=
    center_eq_bot_of_mulEquiv eΩ hcΩ
  have hcX : Subgroup.center X = ⊥ := center_eq_bot_of_mulEquiv e hcProj
  haveI hSP : IsSimpleGroup (StatedProj (StatedOmega (StatedQuadPlus 3 K))) :=
    CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadPlus
      (K := K) (n := 3) (by norm_num)
  have hSX : IsSimpleGroup X := e.isSimpleGroup
  have hcardX : Nat.card X = ordA 3 (2 ^ k) := by
    rw [Nat.card_congr eX.toEquiv]
    exact natCard_omegaPlus_six hKcard hk
  exact quotient_center_simple_and_card hcX hcardX

theorem quotient_center_of_isOmega8m {X : Type} [Group X] {k : ℕ} (hX : IsOmega8m X k) :
    IsSimpleGroup (X ⧸ center X) ∧ Nat.card (X ⧸ center X) = ordTwistedD 4 (2 ^ k) := by
  classical
  have hSC : StatedClassicalModel X .POmegaMinus 4 2 k :=
    CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide)
  have hSX : IsSimpleGroup X := CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hSC
  have hcard : Nat.card X = ordTwistedD 4 (2 ^ k) :=
    (CFSG.Timmesfeld.card_statedClassicalModel_two hSC).2.2.2.2 rfl
  obtain ⟨-, K, hKf, hKfin, hKcard, b, c, hirr, ⟨e⟩⟩ := hSC
  letI := hKf
  letI := hKfin
  haveI hchar : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hKcard
  let Q : QuadraticForm K (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K) :=
    CFSG.LieType.Universal.Spin.quadMinus 4 K b c
  have hQ : ⇑Q = StatedQuadMinus 4 K b c := CFSG.LieType.Universal.Spin.coe_quadMinus 4 K b c
  let P := CFSG.ClassicalGroups.Orthogonal.minusPair (K := K) (b := b) (c := c) (n := 4)
    (⟨0, by norm_num⟩ : Fin (4 - 1))
  have hv : ∃ v, Q v ≠ 0 := by
    refine ⟨P.e + P.f, ?_⟩
    rw [CFSG.Timmesfeld.ClassicalOrders.map_add_eq_one_of_hypPair P]
    exact one_ne_zero
  have hbot := CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot hQ hv
  let eΩ : StatedProj (StatedOmega (StatedQuadMinus 4 K b c)) ≃*
      StatedOmega (StatedQuadMinus 4 K b c) :=
    (CFSG.RankThree.PartOne.KFU.equivProjOfScalarsBot _ hbot).symm
  have hcΩ : Subgroup.center (StatedOmega (StatedQuadMinus 4 K b c)) = ⊥ := by
    rw [CFSG.LieType.Universal.Spin.center_statedOmega_quadMinus (n := 4) (by norm_num) hirr,
      hbot]
  have hcProj : Subgroup.center (StatedProj (StatedOmega (StatedQuadMinus 4 K b c))) = ⊥ :=
    center_eq_bot_of_mulEquiv eΩ hcΩ
  have hcX : Subgroup.center X = ⊥ := center_eq_bot_of_mulEquiv e hcProj
  exact quotient_center_simple_and_card hcX hcard

end CFSG.LocalAnalysis.UniquenessCase.UC22.NoTransv
