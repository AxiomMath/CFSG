module

public import CFSG.Assembly.Defs
public import CFSG.Assembly.LargeEvenDefs
import CFSG.Assembly.OrderReductions.LinearOrders
import CFSG.Open.StatedAPI
import CFSG.Adapters.StatedQuasisimple
import CFSG.ClassicalInvolution.PerfectCase.Basic
import CFSG.Foundations.SteinbergCADefinitionNodes
import CFSG.LieType.SemisimpleCentralizers.HeldSLFacts
import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaCard
import CFSG.LocalAnalysis.StandardType.GGTriD4NoneMarking
import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalResU3ThreeSolv
import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIILinearFiveTwo
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearSmall
import CFSG.CharacterTheory.Semidihedral.OddFieldLift
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
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
import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIL3Rigid
import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIILinearRigid
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSmallSourceLinear
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryDescent
import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
import CFSG.Walter.Defs
import CFSG.Walter.PSL2Facts.Even
import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.StandardType.GGQ2Frame.LinBlocks

open CFSG CFSG.Assembly CFSG.Open CFSG.StandardType Matrix

private theorem isQuasisimple_statedSL {L : Type} [Field L] [Finite L] {n : ℕ}
    (hn : 2 ≤ n) (h4 : n = 2 → 4 ≤ Nat.card L) :
    CFSG.IsQuasisimple ↥(StatedSL n L) := by
  rcases eq_or_lt_of_le hn with hn2 | hn3
  · subst hn2
    have hOpenSL : CFSG.Open.IsQuasisimple (SpecialLinearGroup (Fin 2) L) :=
      CFSG.ClassicalInvolution.isQuasisimple_specialLinearGroup_two (h4 rfl)
    have hOpen : CFSG.Open.IsQuasisimple ↥(StatedSL 2 L) :=
      (CFSG.Open.IsQuasisimple.congr
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 L)).mp hOpenSL
    exact (CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.1.mpr hOpen
  · have h := CFSG.Open.StatedAPI.isQuasisimple_statedSL_of_two_le
        (m := n - 1) (by omega) L
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ n)] at h

private theorem commutator_generalLinear_eq_statedSL {L : Type} [Field L] {n : ℕ}
    (hq : CFSG.IsQuasisimple ↥(StatedSL n L)) :
    commutator (GL (Fin n) L) = StatedSL n L := by
  let D : GL (Fin n) L →* Lˣ := Matrix.GeneralLinearGroup.det
  have hD : D.ker = StatedSL n L := (CFSG.Open.StatedAPI.statedSL_eq_ker_det n L).symm
  have hperf : Group.IsPerfect ↥D.ker := by
    rw [hD]
    exact hq.1
  have hcomm : commutator (GL (Fin n) L) = D.ker := by
    refine le_antisymm (Abelianization.commutator_subset_ker D) ?_
    calc D.ker = ⁅D.ker, D.ker⁆ := (Subgroup.isPerfect_iff.mp hperf).symm
      _ ≤ ⁅(⊤ : Subgroup (GL (Fin n) L)), ⊤⁆ := Subgroup.commutator_mono le_top le_top
      _ = commutator (GL (Fin n) L) := (_root_.commutator_def _).symm
  rw [hcomm, hD]

theorem largeEvenMarking_commutator_of_mulEquiv_gl {G : Type} [Group G] {L : Type} [Field L]
    [Finite L] {n f : ℕ} (hL : Nat.card L = 2 ^ f) (hf : 1 ≤ f) (hn : 2 ≤ n)
    (hnf : n = 2 → 2 ≤ f) {B : Subgroup G}
    (e : ↥B ≃* Matrix.GeneralLinearGroup (Fin n) L) :
    CFSG.StandardType.LargeEvenMarking ↥⁅B, B⁆
      (fun lab _ _ _ _ _ => lab = (⟨.A, n - 1, f⟩ : CFSG.Assembly.LargeEvenLabel)) := by
  have h4f : n = 2 → 4 ≤ 2 ^ f := fun hn2 =>
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (hnf hn2)
  have h4 : n = 2 → 4 ≤ Nat.card L := by
    rw [hL]
    exact h4f
  have hq' : CFSG.IsQuasisimple ↥(StatedSL n L) := isQuasisimple_statedSL hn h4
  have hq : CFSG.Assembly.IsQuasisimple ↥(StatedSL n L) :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.1.mp hq'
  have hlab : LargeEvenInLambda2 (⟨.A, n - 1, f⟩ : LargeEvenLabel) := by
    refine ⟨hf, by show 1 ≤ n - 1; omega, ?_⟩
    intro h
    have hn2 : n = 2 := by
      have h' : n = 1 + 1 := (Nat.sub_eq_iff_eq_add (show 1 ≤ n by omega)).mp h
      simpa using h'
    exact hnf hn2
  have hAdm : CFSG.Open.StatedLieAdmissible .PSL ((n - 1) + 1) 2 f := by
    refine ⟨Nat.prime_two, hf, by omega, ?_, ?_⟩ <;>
    · rintro h
      obtain ⟨h1, h2⟩ := Prod.mk.inj h
      have := h4f (by omega)
      omega
  have hmodel : CFSG.Open.StatedClassicalModel
      (CFSG.Open.StatedProj (StatedSL ((n - 1) + 1) L))
      .PSL ((n - 1) + 1) 2 f :=
    ⟨hAdm, L, inferInstance, inferInstance, hL, ⟨MulEquiv.refl _⟩⟩
  have hn1 : (n - 1) + 1 = n := Nat.sub_add_cancel (by omega)
  have hhas' : GGHasLabel (⟨.A, n - 1, f⟩ : LargeEvenLabel)
      (CFSG.Open.StatedProj (StatedSL ((n - 1) + 1) L)) :=
    ggHasLabel_typeA (n := n - 1) (f := f) hmodel
  have hhas : GGHasLabel (⟨.A, n - 1, f⟩ : LargeEvenLabel)
      (StatedSL ((n - 1) + 1) L ⧸ Subgroup.center (StatedSL ((n - 1) + 1) L)) := by
    obtain ⟨K, hF, hFin, hK, ⟨eK⟩⟩ := hhas'
    obtain ⟨eC⟩ := CFSG.LieType.SemisimpleCentralizers.Held.nonempty_quotientCenter_equiv_statedProj
      (MulEquiv.refl (StatedSL ((n - 1) + 1) L))
    exact ⟨K, hF, hFin, hK, ⟨eC.trans eK⟩⟩
  have hhasn : GGHasLabel (⟨.A, n - 1, f⟩ : LargeEvenLabel)
      (StatedSL n L ⧸ Subgroup.center (StatedSL n L)) := hn1 ▸ hhas
  have hmarkSL : LargeEvenMarking ↥(StatedSL n L)
      (fun lab _ _ _ _ _ => lab = (⟨.A, n - 1, f⟩ : LargeEvenLabel)) :=
    largeEvenMarking_of_hasLabel hq hlab hhasn
  have hcomm := commutator_generalLinear_eq_statedSL hq'
  let ec : ↥⁅B, B⁆ ≃* ↥(StatedSL n L) :=
    (CFSG.ComponentClassification.RankTwoHypIILinear.commutatorEquivOfMulEquiv
      (W := G) (G := GL (Fin n) L) (N := B) e).trans
      (MulEquiv.subgroupCongr hcomm)
  exact largeEvenMarking_of_mulEquiv ec hmarkSL

theorem relIndex_commutator_of_mulEquiv_gl {G : Type} [Group G] {L : Type} [Field L] [Finite L]
    {n : ℕ} (hn : 2 ≤ n) (hnL : n = 2 → 4 ≤ Nat.card L) {B : Subgroup G}
    (e : ↥B ≃* Matrix.GeneralLinearGroup (Fin n) L) :
    (⁅B, B⁆ : Subgroup G).relIndex B = Nat.card L - 1 := by
  have hq' : CFSG.IsQuasisimple ↥(StatedSL n L) := isQuasisimple_statedSL hn hnL
  have hcomm := commutator_generalLinear_eq_statedSL hq'
  let ec : ↥⁅B, B⁆ ≃* ↥(StatedSL n L) :=
    (CFSG.ComponentClassification.RankTwoHypIILinear.commutatorEquivOfMulEquiv
      (W := G) (G := GL (Fin n) L) (N := B) e).trans
      (MulEquiv.subgroupCongr hcomm)
  have hHfin : Finite ↥⁅B, B⁆ := Finite.of_equiv (StatedSL n L) ec.toEquiv.symm
  have hrel := Subgroup.relIndex_mul_card (H := ⁅B, B⁆) (K := B)
  rw [inf_of_le_left (Subgroup.commutator_le_self B)] at hrel
  have hBcard : Nat.card ↥B = Nat.card (GL (Fin n) L) := Nat.card_congr e.toEquiv
  have hHcard : Nat.card ↥⁅B, B⁆ = Nat.card (StatedSL n L) := Nat.card_congr ec.toEquiv
  have hGLcard : Nat.card (GL (Fin n) L) = Nat.card Lˣ * Nat.card (StatedSL n L) := by
    rw [CFSG.OrderReductions.LinearOrders.card_generalLinear_eq_units_mul_specialLinear L n
      (by omega), ← CFSG.Open.StatedAPI.card_statedSL]
  have hmul : (⁅B, B⁆ : Subgroup G).relIndex B * Nat.card ↥⁅B, B⁆ =
      Nat.card Lˣ * Nat.card ↥⁅B, B⁆ := by
    calc (⁅B, B⁆ : Subgroup G).relIndex B * Nat.card ↥⁅B, B⁆ = Nat.card ↥B := hrel
      _ = Nat.card (GL (Fin n) L) := hBcard
      _ = Nat.card Lˣ * Nat.card (StatedSL n L) := hGLcard
      _ = Nat.card Lˣ * Nat.card ↥⁅B, B⁆ := by rw [hHcard]
  have hHpos : 0 < Nat.card ↥⁅B, B⁆ := @Nat.card_pos ↥⁅B, B⁆ ⟨1⟩ hHfin
  have hcancel := Nat.mul_right_cancel hHpos hmul
  rw [Nat.card_units L] at hcancel
  exact hcancel

theorem not_isComponentOf_commutator_of_mulEquiv_gl {G : Type} [Group G] {L : Type} [Field L]
    [Finite L] {n : ℕ} (hn : n ≤ 1 ∨ (n = 2 ∧ Nat.card L = 2)) {B : Subgroup G}
    (e : ↥B ≃* Matrix.GeneralLinearGroup (Fin n) L) (X : Subgroup G) :
    ¬ CFSG.Assembly.IsComponentOf X ⁅B, B⁆ := by
  have hB : Group.IsSolvable ↥B := by
    rcases hn with hn1 | ⟨hn2, hcard⟩
    · rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · subst hn0
        have hsub : Subsingleton ↥B :=
          ⟨fun a b => e.injective (Subsingleton.elim (e a) (e b))⟩
        exact Group.isSolvable_of_comm fun a b => hsub.elim (a * b) (b * a)
      · have hn1' : n = 1 := by omega
        have hsol : Group.IsSolvable (GL (Fin n) L) := by
          rw [hn1']
          exact CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_small_solvable
            1 L (Or.inl rfl)
        exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
    · subst hn2
      have hsol : Group.IsSolvable (GL (Fin 2) L) :=
        CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_small_solvable
          2 L (Or.inr ⟨rfl, Or.inl hcard⟩)
      exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hcomm : Group.IsSolvable ↥⁅B, B⁆ :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (Subgroup.commutator_le_self B))
      (Subgroup.inclusion_injective _)
  exact CFSG.StandardType.ResU3Three.not_isComponentOf_of_isSolvable hcomm

end CFSG.StandardType.GGQ2Frame.LinBlocks
