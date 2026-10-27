module

public import CFSG.LocalAnalysis.StandardType.GGHalfFiveInnAll
public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagConcl
public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagOmegaQuasisimple
public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagOmegaFour
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockOmegaIsoOneLinear
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.OrtHFixed
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogQuadraticNormalForms
import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalResU3ThreeSolv
public import CFSG.RankThree.Classical.SteinbergBYOrthogonalGates
public import CFSG.RankThree.PartOne.AUTSL.OmegaOut
public import CFSG.LocalAnalysis.StandardType.GGNbrLangKGInputs
public import CFSG.OddTranspositions.PartFour.ThirteenListExtTrialityOrthOtherMinus
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphismsCongr
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBoundBase
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataCoordinateRegular
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataReindexGroups
public import CFSG.RankThree.PartOne.KF.ClsOmega
public import CFSG.LocalAnalysis.StandardType.GGAssemblyThreeHypSix
public import CFSG.LocalAnalysis.StandardType.GGRootCentKGMarking
public import CFSG.Timmesfeld.Orders.Distinct
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallL4Klein
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalGroups.SpecialLinear.ComponentCartanRankDivisible
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3TypeDet
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIOrthogonalUnitary4
public import CFSG.RankThree.PartOne.S11d.OrthSplitFixed
public import CFSG.RankThree.PartOne.S11d.OrthGoodSingle
public import CFSG.Timmesfeld.RankOne.SL2
public import CFSG.ClassicalGroups.SpecialLinear.DiagonalTorusRank
public import CFSG.LieType.SpecialLinear.BinaryDescent.Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsRootModule
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.KeyAbstract
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.OrtHShell
import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Inner
import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Split

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.Open (StatedOmega)

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K] [CharP K 2]

omit [DecidableEq ι] [Finite K] in
private theorem even_card_of_polarBilin_nondegenerate (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) : Even (Fintype.card ι) :=
  Module.finrank_fintype_fun_eq_card (R := K) (η := ι) ▸
    CFSG.ComponentClassification.UnbalancedCatalog.even_finrank_of_charTwo Φ hΦ

theorem not_isComponentOf_statedOmega_of_card_le_three (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h3 : Fintype.card ι ≤ 3)
    (C : Subgroup (GL ι K)) : ¬ IsComponentOf C (StatedOmega ⇑Φ) := by
  have hfr : Module.finrank K (ι → K) ≤ 2 := by
    rw [Module.finrank_fintype_fun_eq_card]
    obtain ⟨m, hm⟩ := even_card_of_polarBilin_nondegenerate Φ hΦ
    omega
  have hcomm : ∀ a b : CFSG.RankThree.Classical2.orthDerived Φ, a * b = b * a :=
    fun a b => Subtype.ext
      (CFSG.HardMathSupport.Dickson.Sec6.I1431.t6orth_commute_orthDerived_of_finrank_le_two
        hΦ hfr a.2 b.2)
  have hS : Group.IsSolvable ↥(StatedOmega ⇑Φ) := by
    refine Group.isSolvable_of_comm fun a b => ?_
    apply (CFSG.RankThree.PartOne.statedOmegaOrthEquiv (Q := Φ) rfl).injective
    rw [map_mul, map_mul]
    exact hcomm _ _
  exact ResU3Three.not_isComponentOf_of_isSolvable hS

theorem ggE0Concl_statedOmega_of_six_le_or_minus (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (h : 6 ≤ Fintype.card ι ∨ (Fintype.card ι = 4 ∧
      ¬ ∃ T : Submodule K (ι → K), Module.finrank K T = 2 ∧ ∀ x ∈ T, Φ x = 0))
    (C : Subgroup (GL ι K)) (hC : IsComponentOf C (StatedOmega ⇑Φ)) :
    GGE0Concl (StatedOmega ⇑Φ) C := by
  obtain ⟨t, n, f, hmodel⟩ := exists_statedClassicalModel_statedOmega Φ hΦ h
  exact ggE0Concl_of_isQuasisimple (isQuasisimple_statedOmega Φ hΦ h) hmodel C hC

theorem ggE0Concl_statedOmega_four_plus (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h4 : Fintype.card ι = 4)
    (hplus : ∃ T : Submodule K (ι → K), Module.finrank K T = 2 ∧ ∀ x ∈ T, Φ x = 0)
    (C : Subgroup (GL ι K)) (hC : IsComponentOf C (StatedOmega ⇑Φ)) :
    GGE0Concl (StatedOmega ⇑Φ) C := by
  obtain ⟨f, hmodel⟩ := statedClassicalModel_of_isComponentOf_statedOmega_four Φ hΦ h4 hplus hC
  exact ggE0Concl_of_inner
    (exists_mem_conj_eq_of_isComponentOf_statedOmega_four Φ hΦ h4 hplus hC)
    (largeEvenMarking_inn_of_statedClassicalModel hC.2.2 hmodel)

theorem ggE0Concl_statedOmega (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (C : Subgroup (GL ι K))
    (hC : IsComponentOf C (StatedOmega ⇑Φ)) : GGE0Concl (StatedOmega ⇑Φ) C := by
  obtain ⟨k, hk⟩ := even_card_of_polarBilin_nondegenerate Φ hΦ
  by_cases h3 : Fintype.card ι ≤ 3
  · exact absurd hC (not_isComponentOf_statedOmega_of_card_le_three Φ hΦ h3 C)
  by_cases hplus : Fintype.card ι = 4 ∧
      ∃ T : Submodule K (ι → K), Module.finrank K T = 2 ∧ ∀ x ∈ T, Φ x = 0
  · exact ggE0Concl_statedOmega_four_plus Φ hΦ hplus.1 hplus.2 C hC
  · refine ggE0Concl_statedOmega_of_six_le_or_minus Φ hΦ ?_ C hC
    by_cases h4 : Fintype.card ι = 4
    · exact Or.inr ⟨h4, fun hT => hplus ⟨h4, hT⟩⟩
    · left
      omega

theorem largeEvenMarking_of_isComponentOf_statedOmega
    (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (C : Subgroup (GL ι K))
    (hC : IsComponentOf C (StatedOmega ⇑Φ)) :
    LargeEvenMarking ↥C (fun _ _ _ _ _ _ => True) := by
  by_cases h3 : Fintype.card ι ≤ 3
  · exact (not_isComponentOf_statedOmega_of_card_le_three Φ hΦ h3 C hC).elim
  by_cases hplus : Fintype.card ι = 4 ∧
      ∃ T : Submodule K (ι → K), Module.finrank K T = 2 ∧ ∀ x ∈ T, Φ x = 0
  · obtain ⟨f, hmodel⟩ :=
      statedClassicalModel_of_isComponentOf_statedOmega_four Φ hΦ hplus.1 hplus.2 hC
    exact largeEvenMarking_mono (fun _ _ _ _ _ _ _ => trivial)
      (largeEvenMarking_inn_of_statedClassicalModel hC.2.2 hmodel)
  · have hdim : 6 ≤ Fintype.card ι ∨ (Fintype.card ι = 4 ∧
        ¬ ∃ T : Submodule K (ι → K), Module.finrank K T = 2 ∧ ∀ x ∈ T, Φ x = 0) := by
      by_cases h4 : Fintype.card ι = 4
      · exact Or.inr ⟨h4, fun hT => hplus ⟨h4, hT⟩⟩
      · obtain ⟨k, hk⟩ := even_card_of_polarBilin_nondegenerate Φ hΦ
        left
        omega
    obtain ⟨t, n, f, hmodel⟩ := exists_statedClassicalModel_statedOmega Φ hΦ hdim
    obtain rfl := GGHalf.eq_of_isComponentOf_isQuasisimple
      (isQuasisimple_statedOmega Φ hΦ hdim) hC
    exact largeEvenMarking_mono (fun _ _ _ _ _ _ _ => trivial)
      (largeEvenMarking_inn_of_statedClassicalModel hC.2.2 hmodel)

end CFSG.StandardType

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.Open (StatedQuadPlus StatedProj StatedOmega StatedScalars StatedClassicalModel)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointAction
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.PartOne.AUTSL
open CFSG.LieType.Universal.Spin (quadPlus quadMinus)

variable {K : Type} [Field K]

private theorem mulAut_congr_congr_symm {G H : Type} [Group G] [Group H]
    (e : G ≃* H) (a : MulAut H) :
    MulAut.congr e (MulAut.congr e.symm a) = a := by
  apply MulEquiv.ext
  intro x
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    MulEquiv.apply_symm_apply]

theorem largeEvenMarking_omegaPlus_inn
    {X : Type} [Group X] (hX : CFSG.Assembly.IsQuasisimple X) {m f : ℕ} (hm : 4 ≤ m)
    (hM : StatedClassicalModel (X ⧸ Subgroup.center X) .POmegaPlus m 2 f) :
    LargeEvenMarking X (fun lab R _ I _ _ => GGChevStTag lab ∧ I = LargeEvenInnSet R) := by
  have hf : 1 ≤ f := hM.1.2.1
  have hlab : LargeEvenInLambda2 (⟨.D, m, f⟩ : LargeEvenLabel) := by
    refine ⟨hf, ?_⟩
    simpa using (by omega : 3 ≤ m)
  have hChev : GGChevStTag (⟨.D, m, f⟩ : LargeEvenLabel) := by
    simp [GGChevStTag]
  refine ⟨hX.1, ⟨.D, m, f⟩, hlab, ?_⟩
  have hraw : LargeEvenRawDatum (⟨.D, m, f⟩ : LargeEvenLabel) (fun R _ I _ =>
      Nonempty (X ⧸ Subgroup.center X ≃* R) ∧ I = LargeEvenInnSet R) := by
    rw [LargeEvenRawDatum]
    simp only [if_neg (by omega : m ≠ 3)]
    obtain ⟨K, hF, hfin, hK, hQ⟩ := recipeOmegaPlus_of_statedClassicalModel hM
    exact ⟨K, hF, hfin, hK, ⟨hQ, rfl⟩⟩
  refine largeEvenRawDatum_mono (fun R _ I F hRI => ?_) hraw
  obtain ⟨⟨e⟩, hI⟩ := hRI
  haveI : IsSimpleGroup (X ⧸ Subgroup.center X) := hX.2
  refine ⟨e.symm.isSimpleGroup, ?_, e, hChev, hI⟩
  obtain ⟨a, b, hab⟩ := exists_mul_ne_mul_centerQuot_of_perfect hX.1 inferInstance
  exact ⟨e a, e b, fun h => hab (e.injective (by simpa using h))⟩

private theorem closure_largeEvenInnSet (R : Type) [Group R] :
    Subgroup.closure (LargeEvenInnSet R) = inner R := by
  apply le_antisymm
  · exact (Subgroup.closure_le (K := inner R)).2 (by rintro _ ⟨r, rfl⟩; exact ⟨r, rfl⟩)
  · exact Subgroup.subset_closure

private theorem kgInducedAut_induces' {X : Type} [Group X] {R : Type} [Group R]
    (θ : X ⧸ Subgroup.center X ≃* R) (α : MulAut X) :
    LargeEvenInduces θ (fun j k : X => k = α j) (kgInducedAut θ α) := by
  intro l l' hl
  rw [hl]
  exact ggInducedAut_apply θ α l

private theorem centerQuotAut_eq_congr_bot {X : Type} [Group X]
    (hbot : Subgroup.center X = ⊥) (a : MulAut X) :
    MulAut.congr ((QuotientGroup.quotientMulEquivOfEq hbot).trans
      (QuotientGroup.quotientBot (G := X))) (centerQuotAut X a) = a := by
  apply MulEquiv.ext
  intro x
  obtain ⟨q, rfl⟩ := ((QuotientGroup.quotientMulEquivOfEq hbot).trans
    (QuotientGroup.quotientBot (G := X))).surjective x
  induction q using QuotientGroup.induction_on with
  | H y =>
    have hsymm : (QuotientGroup.quotientMulEquivOfEq hbot).symm
        (QuotientGroup.mk y) = QuotientGroup.mk y := by
      rw [← QuotientGroup.quotientMulEquivOfEq_mk hbot y, MulEquiv.symm_apply_apply]
    rfl

end CFSG.StandardType

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.Open (StatedQuadMinus StatedProj StatedOmega StatedScalars StatedClassicalModel)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointAction
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.PartOne.AUTSL
open CFSG.LieType.Universal.Spin (quadPlus quadMinus)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem largeEvenMarking_omegaMinus_inn
    {X : Type} [Group X] (hX : CFSG.Assembly.IsQuasisimple X) {m f : ℕ} (hm : 4 ≤ m)
    (hM : StatedClassicalModel (X ⧸ Subgroup.center X) .POmegaMinus m 2 f) :
    LargeEvenMarking X (fun lab R _ I _ _ => GGChevStTag lab ∧ I = LargeEvenInnSet R) := by
  have hf : 1 ≤ f := hM.1.2.1
  have hlab : LargeEvenInLambda2 (⟨.twD, m, f⟩ : LargeEvenLabel) := by
    refine ⟨hf, ?_⟩
    simpa using (by omega : 2 ≤ m)
  have hChev : GGChevStTag (⟨.twD, m, f⟩ : LargeEvenLabel) := by
    simp [GGChevStTag]
  refine ⟨hX.1, ⟨.twD, m, f⟩, hlab, ?_⟩
  have hraw : LargeEvenRawDatum (⟨.twD, m, f⟩ : LargeEvenLabel) (fun R _ I _ =>
      Nonempty (X ⧸ Subgroup.center X ≃* R) ∧ I = LargeEvenInnSet R) := by
    rw [LargeEvenRawDatum]
    simp only [if_neg (by omega : m ≠ 2), if_neg (by omega : m ≠ 3)]
    obtain ⟨K, hF, hfin, hK, b, c, hirr, hQ⟩ := recipeOmegaMinus_of_statedClassicalModel hM
    exact ⟨K, hF, hfin, hK, b, c, hirr, ⟨hQ, rfl⟩⟩
  refine largeEvenRawDatum_mono (fun R _ I F hRI => ?_) hraw
  obtain ⟨⟨e⟩, hI⟩ := hRI
  haveI : IsSimpleGroup (X ⧸ Subgroup.center X) := hX.2
  refine ⟨e.symm.isSimpleGroup, ?_, e, hChev, hI⟩
  obtain ⟨a, b, hab⟩ := exists_mul_ne_mul_centerQuot_of_perfect hX.1 inferInstance
  exact ⟨e a, e b, fun h => hab (e.injective (by simpa using h))⟩

end CFSG.StandardType

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.Open (StatedProj StatedOmega StatedClassicalModel StatedSL)

theorem largeEvenMarking_D3_inn {X : Type} [Group X]
    (hX : CFSG.Assembly.IsQuasisimple X) {f : ℕ}
    (hM : StatedClassicalModel (X ⧸ Subgroup.center X) .PSL 4 2 f) :
    LargeEvenMarking X (fun lab R _ I _ _ => GGChevStTag lab ∧ I = LargeEvenInnSet R) := by
  have hf : 1 ≤ f := hM.1.2.1
  have hlab : LargeEvenInLambda2 (⟨.D, 3, f⟩ : LargeEvenLabel) := by
    refine ⟨hf, by norm_num⟩
  have hChev : GGChevStTag (⟨.D, 3, f⟩ : LargeEvenLabel) := by
    simp [GGChevStTag]
  refine ⟨hX.1, ⟨.D, 3, f⟩, hlab, ?_⟩
  have hraw : LargeEvenRawDatum (⟨.D, 3, f⟩ : LargeEvenLabel) (fun R _ I _ =>
      Nonempty (X ⧸ Subgroup.center X ≃* R) ∧ I = LargeEvenInnSet R) := by
    rw [LargeEvenRawDatum]
    obtain ⟨K, hF, hfin, hK, ⟨e⟩⟩ := recipeLinear_of_statedClassicalModel hM
    refine ⟨K, hF, hfin, hK, ⟨e⟩, ?_⟩
    apply le_antisymm
    · refine matConjImage_gl_subset_inn (K := K) (d := 4) ?_
      have hodd : Odd (Nat.card Kˣ) := by
        rw [Nat.card_units, hK]
        exact CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by omega)
      rw [show (4 : ℕ) = 2 * 2 by norm_num]
      exact Nat.Coprime.mul_right (Nat.coprime_two_right.mpr hodd)
        (Nat.coprime_two_right.mpr hodd)
    · exact innSet_subset_matConjImage (LargeEvenSLGroup (Fin 4) K) Set.univ (fun _ _ => Set.mem_univ _)
  refine largeEvenRawDatum_mono (fun R _ I F hRI => ?_) hraw
  obtain ⟨⟨e⟩, hI⟩ := hRI
  haveI : IsSimpleGroup (X ⧸ Subgroup.center X) := hX.2
  refine ⟨e.symm.isSimpleGroup, ?_, e, hChev, hI⟩
  obtain ⟨a, b, hab⟩ := exists_mul_ne_mul_centerQuot_of_perfect hX.1 inferInstance
  exact ⟨e a, e b, fun h => hab (e.injective (by simpa using h))⟩

end CFSG.StandardType

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.Open (StatedProj StatedOmega StatedClassicalModel StatedSL)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.PartOne.AUTSL
open CFSG.LieType.Universal.Spin (quadPlus)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem largeEvenMarking_A1_inn {X : Type} [Group X]
    (hX : CFSG.Assembly.IsQuasisimple X) {f : ℕ} (hf2 : 2 ≤ f)
    (hM : StatedClassicalModel (X ⧸ Subgroup.center X) .PSL 2 2 f) :
    LargeEvenMarking X (fun lab R _ I _ _ => GGChevStTag lab ∧ I = LargeEvenInnSet R) := by
  have hf : 1 ≤ f := by omega
  have hlab : LargeEvenInLambda2 (⟨.A, 1, f⟩ : LargeEvenLabel) := by
    refine ⟨hf, by norm_num, ?_⟩
    simpa using hf2
  have hChev : GGChevStTag (⟨.A, 1, f⟩ : LargeEvenLabel) := by
    simp [GGChevStTag]
  refine ⟨hX.1, ⟨.A, 1, f⟩, hlab, ?_⟩
  have hraw : LargeEvenRawDatum (⟨.A, 1, f⟩ : LargeEvenLabel) (fun R _ I _ =>
      Nonempty (X ⧸ Subgroup.center X ≃* R) ∧ I = LargeEvenInnSet R) := by
    rw [LargeEvenRawDatum]
    obtain ⟨K, hF, hfin, hK, ⟨e⟩⟩ := recipeLinear_of_statedClassicalModel hM
    refine ⟨K, hF, hfin, hK, ⟨e⟩, ?_⟩
    apply le_antisymm
    · refine matConjImage_gl_subset_inn (K := K) (d := 2) ?_
      have hodd : Odd (Nat.card Kˣ) := by
        rw [Nat.card_units, hK]
        exact CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by omega)
      exact Nat.coprime_two_right.mpr hodd
    · exact innSet_subset_matConjImage (LargeEvenSLGroup (Fin 2) K) Set.univ (fun _ _ => Set.mem_univ _)
  refine largeEvenRawDatum_mono (fun R _ I F hRI => ?_) hraw
  obtain ⟨⟨e⟩, hI⟩ := hRI
  haveI : IsSimpleGroup (X ⧸ Subgroup.center X) := hX.2
  refine ⟨e.symm.isSimpleGroup, ?_, e, hChev, hI⟩
  obtain ⟨a, b, hab⟩ := exists_mul_ne_mul_centerQuot_of_perfect hX.1 inferInstance
  exact ⟨e a, e b, fun h => hab (e.injective (by simpa using h))⟩
end CFSG.StandardType

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.Open (StatedProj StatedOmega StatedClassicalModel StatedSL)
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.PartOne
open CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.RankThree.Classical2

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_largeEvenMarking_fixedFactor_left_not_mem_inner
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) [Nontrivial V]
    {p : ℕ} {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x)
    (M : SplitFourModel (Q.comp (fixedSpace x).subtype))
    {σ : K ≃+* K} {S : V ≃+ V}
    (hS : ∀ (c : K) v, S (c • v) = σ c • S v)
    (hSx : ∀ v, S (x v) = x (S v)) (hσ : ∃ c, σ c ≠ c)
    {α : MulAut (ProjOrthDerived Q)} (hα : ActsBySemilinear Q S α)
    {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf2 : 2 ≤ f)
    (f' : MulAut ↥(fixedFactorImage hx (splitFourFactors M.e 0)))
    (hf' : ∀ g : ↥(fixedFactorImage hx (splitFourFactors M.e 0)),
      ((f' g : ↥(fixedFactorImage hx (splitFourFactors M.e 0))) : ProjOrthDerived Q) = α g) :
    LargeEvenMarking ↥(fixedFactorImage hx (splitFourFactors M.e 0))
      (fun lab R _ I _ θ => GGChevStTag lab ∧ I = LargeEvenInnSet R ∧
        ¬ ∃ φ ∈ Subgroup.closure I,
          LargeEvenInduces θ
            (fun j k : ↥(fixedFactorImage hx (splitFourFactors M.e 0)) => k = f' j) φ) := by
  let C := ↥(fixedFactorImage hx (splitFourFactors M.e 0))
  let : Fintype K := Fintype.ofFinite K
  haveI : Fintype V := by
    classical
    let b := Module.finBasis K V
    exact Fintype.ofEquiv (Fin (Module.finrank K V) → K) b.equivFun.symm
  let eC : Matrix.SpecialLinearGroup (Fin 2) K ≃* C := M.leftEquiv hx hQ
  have hq2 : Nat.card K ≠ 2 := by
    intro h
    have hge : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
    rw [h] at hK
    omega
  have hSL : CFSG.Assembly.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) K) :=
    CFSG.StandardType.isQuasisimple_specialLinear (ι := Fin 2) (Q := K)
      (by norm_num) (Or.inr hq2)
  have hX : CFSG.Assembly.IsQuasisimple C :=
    CFSG.Assembly.IsQuasisimple.of_mulEquiv eC.symm hSL
  have hcenterSL : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ :=
    CFSG.Timmesfeld.RankOne.center_SL2_eq_bot K
  have hbot : Subgroup.center C = ⊥ := by
    have h1 := Subgroup.map_center_eq eC
    rw [hcenterSL] at h1
    simpa using h1.symm
  let eQ : (Matrix.SpecialLinearGroup (Fin 2) K ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) ≃*
      (C ⧸ Subgroup.center C) :=
    QuotientGroup.congr (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))
      (Subgroup.center C) eC (Subgroup.map_center_eq eC)
  let eZ : C ⧸ Subgroup.center C ≃* StatedProj (StatedSL 2 K) :=
    eQ.symm.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K)
  have hM : StatedClassicalModel (C ⧸ Subgroup.center C) .PSL 2 2 f := by
    refine ⟨⟨Nat.prime_two, by omega, by norm_num, ?_, ?_⟩, K, inferInstance, inferInstance, ?_, ⟨eZ⟩⟩
    · intro hcon
      have h2' : 2 ^ f = 2 := by simpa using congrArg Prod.snd hcon
      have hge : 4 ≤ 2 ^ f := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
      omega
    · intro hcon
      have h3 : 2 ^ f = 3 := by simpa using congrArg Prod.snd hcon
      have hge : 4 ≤ 2 ^ f := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
      omega
    · simpa only [Nat.card_eq_fintype_card] using hK
  have hmark := largeEvenMarking_A1_inn hX hf2 hM
  have hnotInner : f' ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner C := by
    rintro ⟨c, hc⟩
    have hnot := M.not_inner_left hx hQ hS hSx hσ hα
    apply hnot (c : ProjOrthDerived Q) c.2
    intro g hg
    have hgc := congrArg (fun e : MulAut C => (e ⟨g, hg⟩ : C)) hc
    have hgc0 := congrArg (fun x : C => (x : ProjOrthDerived Q)) hgc
    rw [MulAut.conj_apply] at hgc0
    rw [hf' ⟨g, hg⟩] at hgc0
    change (c : ProjOrthDerived Q) * g * (c : ProjOrthDerived Q)⁻¹ = α g at hgc0
    exact hgc0.symm
  refine largeEvenMarking_mono ?_ hmark
  rintro lab R _ I F θ ⟨hChev, hI⟩
  refine ⟨hChev, hI, ?_⟩
  rintro ⟨φ, hφ, hind⟩
  have hclosure : Subgroup.closure I =
      CFSG.ComponentClassification.OuterAutomorphisms.inner R := by
    rw [hI]
    exact closure_largeEvenInnSet R
  rw [hclosure] at hφ
  have hkgInd : LargeEvenInduces θ (fun j k : C => k = f' j) (kgInducedAut θ f') :=
    kgInducedAut_induces' θ f'
  have huniq := CFSG.LocalAnalysis.GLTheoremA.T171Sh.largeEvenInduces_unique hind hkgInd
    (fun l => ⟨f' l, rfl⟩)
  have hkgInner : kgInducedAut θ f' ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner R := by
    rwa [← huniq]
  have hcqInner : centerQuotAut C f' ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (C ⧸ Subgroup.center C) := by
    rw [← congr_mem_inner_iff θ (centerQuotAut C f')]
    change MulAut.congr θ (centerQuotAut C f') ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner R at hkgInner
    exact hkgInner
  let eBot : C ⧸ Subgroup.center C ≃* C :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans (QuotientGroup.quotientBot (G := C))
  have hcqEq : MulAut.congr eBot (centerQuotAut C f') = f' :=
    centerQuotAut_eq_congr_bot hbot f'
  have hfInner : f' ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner C := by
    rw [← hcqEq]
    exact (congr_mem_inner_iff eBot (centerQuotAut C f')).2 hcqInner
  exact hnotInner hfInner

theorem exists_largeEvenMarking_fixedFactor_right_not_mem_inner
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) [Nontrivial V]
    {p : ℕ} {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x)
    (M : SplitFourModel (Q.comp (fixedSpace x).subtype))
    {σ : K ≃+* K} {S : V ≃+ V}
    (hS : ∀ (c : K) v, S (c • v) = σ c • S v)
    (hSx : ∀ v, S (x v) = x (S v)) (hσ : ∃ c, σ c ≠ c)
    {α : MulAut (ProjOrthDerived Q)} (hα : ActsBySemilinear Q S α)
    {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf2 : 2 ≤ f)
    (f' : MulAut ↥(fixedFactorImage hx (splitFourFactors M.e 1)))
    (hf' : ∀ g : ↥(fixedFactorImage hx (splitFourFactors M.e 1)),
      ((f' g : ↥(fixedFactorImage hx (splitFourFactors M.e 1))) : ProjOrthDerived Q) = α g) :
    LargeEvenMarking ↥(fixedFactorImage hx (splitFourFactors M.e 1))
      (fun lab R _ I _ θ => GGChevStTag lab ∧ I = LargeEvenInnSet R ∧
        ¬ ∃ φ ∈ Subgroup.closure I,
          LargeEvenInduces θ
            (fun j k : ↥(fixedFactorImage hx (splitFourFactors M.e 1)) => k = f' j) φ) := by
  let C := ↥(fixedFactorImage hx (splitFourFactors M.e 1))
  let : Fintype K := Fintype.ofFinite K
  haveI : Fintype V := by
    classical
    let b := Module.finBasis K V
    exact Fintype.ofEquiv (Fin (Module.finrank K V) → K) b.equivFun.symm
  let eC : Matrix.SpecialLinearGroup (Fin 2) K ≃* C := M.rightEquiv hx hQ
  have hq2 : Nat.card K ≠ 2 := by
    intro h
    have hge : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
    rw [h] at hK
    omega
  have hSL : CFSG.Assembly.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) K) :=
    CFSG.StandardType.isQuasisimple_specialLinear (ι := Fin 2) (Q := K)
      (by norm_num) (Or.inr hq2)
  have hX : CFSG.Assembly.IsQuasisimple C :=
    CFSG.Assembly.IsQuasisimple.of_mulEquiv eC.symm hSL
  have hcenterSL : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ :=
    CFSG.Timmesfeld.RankOne.center_SL2_eq_bot K
  have hbot : Subgroup.center C = ⊥ := by
    have h1 := Subgroup.map_center_eq eC
    rw [hcenterSL] at h1
    simpa using h1.symm
  let eQ : (Matrix.SpecialLinearGroup (Fin 2) K ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) ≃*
      (C ⧸ Subgroup.center C) :=
    QuotientGroup.congr (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))
      (Subgroup.center C) eC (Subgroup.map_center_eq eC)
  let eZ : C ⧸ Subgroup.center C ≃* StatedProj (StatedSL 2 K) :=
    eQ.symm.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K)
  have hM : StatedClassicalModel (C ⧸ Subgroup.center C) .PSL 2 2 f := by
    refine ⟨⟨Nat.prime_two, by omega, by norm_num, ?_, ?_⟩, K, inferInstance, inferInstance, ?_, ⟨eZ⟩⟩
    · intro hcon
      have h2' : 2 ^ f = 2 := by simpa using congrArg Prod.snd hcon
      have hge : 4 ≤ 2 ^ f := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
      omega
    · intro hcon
      have h3 : 2 ^ f = 3 := by simpa using congrArg Prod.snd hcon
      have hge : 4 ≤ 2 ^ f := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
      omega
    · simpa only [Nat.card_eq_fintype_card] using hK
  have hmark := largeEvenMarking_A1_inn hX hf2 hM
  have hnotInner : f' ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner C := by
    rintro ⟨c, hc⟩
    have hnot := M.not_inner_right hx hQ hS hSx hσ hα
    apply hnot (c : ProjOrthDerived Q) c.2
    intro g hg
    have hgc := congrArg (fun e : MulAut C => (e ⟨g, hg⟩ : C)) hc
    have hgc0 := congrArg (fun x : C => (x : ProjOrthDerived Q)) hgc
    rw [MulAut.conj_apply] at hgc0
    rw [hf' ⟨g, hg⟩] at hgc0
    change (c : ProjOrthDerived Q) * g * (c : ProjOrthDerived Q)⁻¹ = α g at hgc0
    exact hgc0.symm
  refine largeEvenMarking_mono ?_ hmark
  rintro lab R _ I F θ ⟨hChev, hI⟩
  refine ⟨hChev, hI, ?_⟩
  rintro ⟨φ, hφ, hind⟩
  have hclosure : Subgroup.closure I =
      CFSG.ComponentClassification.OuterAutomorphisms.inner R := by
    rw [hI]
    exact closure_largeEvenInnSet R
  rw [hclosure] at hφ
  have hkgInd : LargeEvenInduces θ (fun j k : C => k = f' j) (kgInducedAut θ f') :=
    kgInducedAut_induces' θ f'
  have huniq := CFSG.LocalAnalysis.GLTheoremA.T171Sh.largeEvenInduces_unique hind hkgInd
    (fun l => ⟨f' l, rfl⟩)
  have hkgInner : kgInducedAut θ f' ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner R := by
    rwa [← huniq]
  have hcqInner : centerQuotAut C f' ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (C ⧸ Subgroup.center C) := by
    rw [← congr_mem_inner_iff θ (centerQuotAut C f')]
    change MulAut.congr θ (centerQuotAut C f') ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner R at hkgInner
    exact hkgInner
  let eBot : C ⧸ Subgroup.center C ≃* C :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans (QuotientGroup.quotientBot (G := C))
  have hcqEq : MulAut.congr eBot (centerQuotAut C f') = f' :=
    centerQuotAut_eq_congr_bot hbot f'
  have hfInner : f' ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner C := by
    rw [← hcqEq]
    exact (congr_mem_inner_iff eBot (centerQuotAut C f')).2 hcqInner
  exact hnotInner hfInner

end CFSG.StandardType

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.Open (StatedProj StatedOmega StatedClassicalModel StatedSL)

theorem largeEvenMarking_twD2_inn {X : Type} [Group X]
    (hX : CFSG.Assembly.IsQuasisimple X) {n : ℕ} (hn : 1 ≤ n)
    (hM : StatedClassicalModel (X ⧸ Subgroup.center X) .PSL 2 2 (2 * n)) :
    LargeEvenMarking X (fun lab R _ I _ _ => GGChevStTag lab ∧ I = LargeEvenInnSet R) := by
  have hlab : LargeEvenInLambda2 (⟨.twD, 2, n⟩ : LargeEvenLabel) := by
    refine ⟨hn, by norm_num⟩
  have hChev : GGChevStTag (⟨.twD, 2, n⟩ : LargeEvenLabel) := by
    simp [GGChevStTag]
  refine ⟨hX.1, ⟨.twD, 2, n⟩, hlab, ?_⟩
  have hraw : LargeEvenRawDatum (⟨.twD, 2, n⟩ : LargeEvenLabel) (fun R _ I _ =>
      Nonempty (X ⧸ Subgroup.center X ≃* R) ∧ I = LargeEvenInnSet R) := by
    rw [LargeEvenRawDatum]
    obtain ⟨K, hF, hfin, hK, ⟨e⟩⟩ := recipeLinear_of_statedClassicalModel hM
    have hK' : Nat.card K = (2 ^ n) ^ 2 := by
      simpa only [pow_two, ← pow_add, two_mul] using hK
    refine ⟨K, hF, hfin, hK', ⟨e⟩, ?_⟩
    apply le_antisymm
    · refine matConjImage_gl_subset_inn (K := K) (d := 2) ?_
      have hodd : Odd (Nat.card Kˣ) := by
        rw [Nat.card_units, hK]
        exact CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by omega)
      exact Nat.coprime_two_right.mpr hodd
    · exact innSet_subset_matConjImage (LargeEvenSLGroup (Fin 2) K) Set.univ (fun _ _ => Set.mem_univ _)
  refine largeEvenRawDatum_mono (fun R _ I F hRI => ?_) hraw
  obtain ⟨⟨e⟩, hI⟩ := hRI
  haveI : IsSimpleGroup (X ⧸ Subgroup.center X) := hX.2
  refine ⟨e.symm.isSimpleGroup, ?_, e, hChev, hI⟩
  obtain ⟨a, b, hab⟩ := exists_mul_ne_mul_centerQuot_of_perfect hX.1 inferInstance
  exact ⟨e a, e b, fun h => hab (e.injective (by simpa using h))⟩

end CFSG.StandardType

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.Open (StatedOmega StatedClassicalModel)

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K] [CharP K 2]

theorem largeEvenMarking_statedOmega_inn (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (h : 6 ≤ Fintype.card ι ∨ (Fintype.card ι = 4 ∧
      ¬ ∃ T : Submodule K (ι → K), Module.finrank K T = 2 ∧ ∀ x ∈ T, Φ x = 0)) :
    LargeEvenMarking ↥(StatedOmega ⇑Φ)
      (fun lab R _ I _ _ => GGChevStTag lab ∧ I = LargeEvenInnSet R) := by
  have hX : CFSG.Assembly.IsQuasisimple ↥(StatedOmega ⇑Φ) :=
    isQuasisimple_statedOmega Φ hΦ h
  rcases exists_statedClassicalModel_statedOmega_cases Φ hΦ h with
    ⟨n, f, hn, hM⟩ | ⟨n, f, hn, hM⟩ | ⟨f, hM⟩ | ⟨f, hM⟩ | ⟨f, hM⟩
  · exact largeEvenMarking_omegaPlus_inn hX hn hM
  · exact largeEvenMarking_omegaMinus_inn hX hn hM
  · exact largeEvenMarking_D3_inn hX hM
  · exact largeEvenMarking_twD3_inn hX hM
  · have hf : 1 ≤ f := by
      have h := hM.1.2.1
      omega
    exact largeEvenMarking_twD2_inn (n := f) hX hf hM

end CFSG.StandardType

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.Open (StatedOmega)
open CFSG.RankThree.PartOne
open CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.RankThree.Classical2
open CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

theorem kgFieldRestriction_statedOmegaFourComponent_of_semilinearPair
    {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} (hd : d = 4)
    (Q : QuadraticForm K (Fin d → K))
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hsplit : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 2 ∧ ∀ x ∈ T, Q x = 0)
    {e : ℕ} (hK : Nat.card K = 2 ^ e) (he2 : 2 ≤ e)
    (g : similarityPairs Q) (hg : g.val.right ≠ 1)
    (C : Subgroup (StatedOmega ⇑Q)) (hC : CFSG.Assembly.IsComponentOf C ⊤)
    (fC : MulAut ↥C)
    (hfC : ∀ c : ↥C, ∀ v : Fin d → K,
      toLinEquiv (Fin d) K (((fC c : ↥C) : StatedOmega ⇑Q) : GL (Fin d) K) v =
        coordinateSemilinearMap g.val
          (toLinEquiv (Fin d) K (((c : ↥C) : StatedOmega ⇑Q) : GL (Fin d) K)
            ((coordinateSemilinearMap g.val).symm v))) :
    GGMarkingAll (K := ↥C) fun _ _ _ I _ θ => kgInducedAut θ fC ∉ I := by
  subst d
  classical
  let V := Fin 4 → K
  let S : V ≃+ V := coordinateSemilinearMap g.val
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he2
  haveI : Nontrivial V := inferInstance
  have hx1 : OddOrderIsometry Q 1 (1 : V ≃ₗ[K] V) :=
    { mem := one_mem _
      pow_eq_one := one_pow 1
      cast_ne_zero := by simpa using (one_ne_zero : (1 : K) ≠ 0)
      regular := fun v hv => hQ.1 v (by
        simpa only [QuadraticMap.polarBilin_apply_apply] using hv) }
  have hfix : fixedSpace (1 : V ≃ₗ[K] V) = ⊤ := by
    ext v
    simp [fixedSpace]
  have h4 : Module.finrank K (fixedSpace (1 : V ≃ₗ[K] V)) = 4 := by
    rw [hfix]
    simp [V, Module.finrank_fintype_fun_eq_card]
  have hsplit_top : ∃ T : Submodule K (⊤ : Submodule K V), Module.finrank K T = 2 ∧
      ∀ u ∈ T, (Q.comp (⊤ : Submodule K V).subtype) u = 0 := by
    obtain ⟨T, hT, hT0⟩ := hsplit
    refine ⟨T.map (Submodule.topEquiv (R := K) (M := V)).symm.toLinearMap, ?_, ?_⟩
    · rw [LinearEquiv.finrank_map_eq]
      exact hT
    · rintro _ ⟨t, ht, rfl⟩
      simpa using hT0 t ht
  have hsplit_fixed : ∃ T : Submodule K (fixedSpace (1 : V ≃ₗ[K] V)),
      Module.finrank K T = 2 ∧
        ∀ u ∈ T, (Q.comp (fixedSpace (1 : V ≃ₗ[K] V)).subtype) u = 0 := by
    rw [hfix]
    exact hsplit_top
  obtain ⟨M⟩ := exists_splitFourModel (Q := Q) (x := (1 : V ≃ₗ[K] V)) hx1 h4 hsplit_fixed hK4
  have hfam := M.family hx1
  have hSF : supportedFixedDerived Q (1 : V ≃ₗ[K] V) = orthDerived Q := by
    rw [← hx1.supportedDerived_fixedSpace, hfix]
    exact supportedDerived_top_eq_orthDerived hQ
  have himg : fixedComponentImage Q (1 : V ≃ₗ[K] V) = ⊤ := by
    unfold fixedComponentImage
    rw [hSF, Subgroup.subgroupOf_self, Subgroup.map_top]
    exact MonoidHom.range_eq_top.mpr piOrth_surjective
  have hcent : centralizerImage Q (1 : V ≃ₗ[K] V) = ⊤ := by
    change centralizerImage Q ((1 : orthDerived Q) : V ≃ₗ[K] V) = ⊤
    rw [centralizerImage_eq (Q := Q) hQ (1 : orthDerived Q)]
    simp
  let D : Fin 2 → Subgroup (ProjOrthDerived Q) :=
    fun i => fixedFactorImage hx1 (splitFourFactors M.e i)
  have hcompD : ∀ i, CFSG.Assembly.IsComponentOf (D i) ⊤ := by
    intro i
    have hle : D i ≤ centralizerImage Q (1 : V ≃ₗ[K] V) := (hfam.2 i).2.1
    have hsub : CFSG.Assembly.IsSubnormal
        ((D i).subgroupOf (centralizerImage Q (1 : V ≃ₗ[K] V))) ⊤ :=
      CFSG.Assembly.IsSubnormal.of_mathlib (hfam.2 i).2.2
    have hq : CFSG.IsQuasisimple ↥(D i) := (hfam.2 i).1
    have hqA : CFSG.Assembly.IsQuasisimple ↥(D i) :=
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hq
    let eD := Subgroup.subgroupOfEquivOfLe hle
    have hqsub : CFSG.Assembly.IsQuasisimple
        ↥((D i).subgroupOf (centralizerImage Q (1 : V ≃ₗ[K] V))) :=
      CFSG.Assembly.IsQuasisimple.of_mulEquiv eD hqA
    have hcompX : CFSG.Assembly.IsComponentOf ((D i).subgroupOf (centralizerImage Q (1 : V ≃ₗ[K] V))) ⊤ :=
      ⟨le_top, hsub, hqsub⟩
    have hmap := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_of_injective hcompX
      (centralizerImage Q (1 : V ≃ₗ[K] V)).subtype
      (centralizerImage Q (1 : V ≃ₗ[K] V)).subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hle, Subgroup.map_top, Subgroup.range_subtype,
      hcent] at hmap
    exact hmap
  have hsupD : D 0 ⊔ D 1 = ⊤ := by
    have h := hfam.1
    rw [himg] at h
    have h2 : (⨆ i : Fin 2, D i) = D 0 ⊔ D 1 := by
      apply le_antisymm
      · refine iSup_le fun i => ?_
        fin_cases i
        · exact le_sup_left
        · exact le_sup_right
      · exact sup_le (le_iSup D 0) (le_iSup D 1)
    rwa [h2] at h
  let H : Subgroup (GL (Fin 4) K) := StatedOmega ⇑Q
  let eΩ : ↥H ≃* ↥(orthDerived Q) :=
    CFSG.RankThree.GF2n.Stroth80.statedOmegaMulEquivDerived (Q := Q) rfl
  let ePi : ↥(orthDerived Q) ≃* ProjOrthDerived Q :=
    MulEquiv.ofBijective (piOrth Q) ⟨piOrth_injective hQ, piOrth_surjective⟩
  let eT : ↥H ≃* ProjOrthDerived Q := eΩ.trans ePi
  have hcoeΩ : ∀ x : ↥H,
      ((eΩ x : orthDerived Q) : V ≃ₗ[K] V) = toLinEquiv (Fin 4) K (x : GL (Fin 4) K) := by
    intro x
    change ((CFSG.RankThree.GF2n.Stroth80.statedOmegaMulEquivDerived (Q := Q) rfl x :
      orthDerived Q) : V ≃ₗ[K] V) = toLinEquiv (Fin 4) K (x : GL (Fin 4) K)
    rfl
  have hpointC : ∀ c : ↥C, eT (fC c) = KCOrthComm.kappa Q g (eT c) := by
    intro c
    change piOrth Q (eΩ ((fC c : ↥C) : ↥H)) =
      KCOrthComm.kappa Q g (piOrth Q (eΩ (c : ↥H)))
    exact (KCOrthComm.kappa_apply Q g (eΩ (c : ↥H)) (eΩ ((fC c : ↥C) : ↥H))
      (fun v => by
        rw [hcoeΩ, hcoeΩ]
        exact hfC c v)).symm
  let CT : Subgroup (ProjOrthDerived Q) := C.map eT.toMonoidHom
  have hCT : CFSG.Assembly.IsComponentOf CT ⊤ := by
    have h := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_of_injective hC
      eT.toMonoidHom eT.injective
    have htop : (⊤ : Subgroup ↥H).map eT.toMonoidHom = ⊤ := by
      rw [Subgroup.map_top]
      exact MonoidHom.range_eq_top.mpr eT.surjective
    simpa [CT, htop] using h
  let eC : ↥C ≃* ↥CT := Subgroup.equivMapOfInjective C eT.toMonoidHom eT.injective
  let fCT : MulAut ↥CT := MulAut.congr eC fC
  have hpointCT : ∀ x : ↥CT,
      ((fCT x : ↥CT) : ProjOrthDerived Q) = KCOrthComm.kappa Q g x := by
    intro x
    let c : ↥C := eC.symm x
    have hx : eC c = x := eC.apply_symm_apply x
    have hf : fCT x = eC (fC c) := by
      simp [fCT, c, MulAut.congr_apply]
    calc
      ((fCT x : ↥CT) : ProjOrthDerived Q)
          = ((eC (fC c) : ↥CT) : ProjOrthDerived Q) := by rw [hf]
      _ = eT (fC c) := rfl
      _ = KCOrthComm.kappa Q g (eT c) := hpointC c
      _ = KCOrthComm.kappa Q g ((eC c : ↥CT) : ProjOrthDerived Q) := rfl
      _ = KCOrthComm.kappa Q g x := by rw [hx]
  have hα : ActsBySemilinear Q S (KCOrthComm.kappa Q g) :=
    CFSG.RankThree.PartOne.actsBySemilinear_kappa Q g
  have hS : ∀ (c : K) v, S (c • v) = g.val.right c • S v :=
    fun c v => coordinateSemilinearMap_smul g.val c v
  have hSx : ∀ v, S ((1 : V ≃ₗ[K] V) v) = (1 : V ≃ₗ[K] V) (S v) := fun v => rfl
  have hσ : ∃ c : K, g.val.right c ≠ c := by
    by_contra h
    push Not at h
    exact hg (RingEquiv.ext h)
  have hcompDopen : ∀ i, CFSG.Open.IsComponentOf (D i) ⊤ := fun i =>
    (CFSG.Assembly.isComponentOf_iff_open).mp (hcompD i)
  have hCTopen : CFSG.Open.IsComponentOf CT ⊤ :=
    (CFSG.Assembly.isComponentOf_iff_open).mp hCT
  rcases CFSG.LocalAnalysis.UniquenessCase.UC22.NatParMax.eq_factor_of_isComponentOf
    hsupD (hcompDopen 0) (hcompDopen 1) hCTopen with hCeq | hCeq
  · let eCD : ↥C ≃* ↥(D 0) := eC.trans (MulEquiv.subgroupCongr hCeq)
    let fD : MulAut ↥(D 0) := MulAut.congr eCD fC
    have hpointD : ∀ x : ↥(D 0),
        ((fD x : ↥(D 0)) : ProjOrthDerived Q) = KCOrthComm.kappa Q g x := by
      intro x
      let c : ↥C := eCD.symm x
      have hx : eCD c = x := eCD.apply_symm_apply x
      have hf : fD x = eCD (fC c) := by
        simp [fD, c, MulAut.congr_apply]
      have hct : ((eCD (fC c) : ↥(D 0)) : ProjOrthDerived Q) =
          KCOrthComm.kappa Q g ((eCD c : ↥(D 0)) : ProjOrthDerived Q) := by
        have h := hpointCT (eC c)
        simpa [fCT, eCD, MulAut.congr_apply, MulEquiv.trans_apply] using h
      calc
        ((fD x : ↥(D 0)) : ProjOrthDerived Q)
            = ((eCD (fC c) : ↥(D 0)) : ProjOrthDerived Q) := by rw [hf]
        _ = KCOrthComm.kappa Q g ((eCD c : ↥(D 0)) : ProjOrthDerived Q) := hct
        _ = KCOrthComm.kappa Q g x := by rw [hx]
    have hmark := exists_largeEvenMarking_fixedFactor_left_not_mem_inner
      (V := V) (Q := Q) hQ hx1 M hS hSx hσ hα hK he2 fD hpointD
    have hmark' : LargeEvenMarking ↥(D 0) fun _ _ _ I _ θ =>
        ¬ ∃ φ ∈ Subgroup.closure I, LargeEvenInduces θ (fun j k : ↥(D 0) => k = fD j) φ :=
      largeEvenMarking_mono (fun lab R _ I F θ h => h.2.2) hmark
    exact kgFieldRestriction_of_oneMarking_congr eCD fC fD (fun x => by simp [fD]) hmark' 
  · let eCD : ↥C ≃* ↥(D 1) := eC.trans (MulEquiv.subgroupCongr hCeq)
    let fD : MulAut ↥(D 1) := MulAut.congr eCD fC
    have hpointD : ∀ x : ↥(D 1),
        ((fD x : ↥(D 1)) : ProjOrthDerived Q) = KCOrthComm.kappa Q g x := by
      intro x
      let c : ↥C := eCD.symm x
      have hx : eCD c = x := eCD.apply_symm_apply x
      have hf : fD x = eCD (fC c) := by
        simp [fD, c, MulAut.congr_apply]
      have hct : ((eCD (fC c) : ↥(D 1)) : ProjOrthDerived Q) =
          KCOrthComm.kappa Q g ((eCD c : ↥(D 1)) : ProjOrthDerived Q) := by
        have h := hpointCT (eC c)
        simpa [fCT, eCD, MulAut.congr_apply, MulEquiv.trans_apply] using h
      calc
        ((fD x : ↥(D 1)) : ProjOrthDerived Q)
            = ((eCD (fC c) : ↥(D 1)) : ProjOrthDerived Q) := by rw [hf]
        _ = KCOrthComm.kappa Q g ((eCD c : ↥(D 1)) : ProjOrthDerived Q) := hct
        _ = KCOrthComm.kappa Q g x := by rw [hx]
    have hmark := exists_largeEvenMarking_fixedFactor_right_not_mem_inner
      (V := V) (Q := Q) hQ hx1 M hS hSx hσ hα hK he2 fD hpointD
    have hmark' : LargeEvenMarking ↥(D 1) fun _ _ _ I _ θ =>
        ¬ ∃ φ ∈ Subgroup.closure I, LargeEvenInduces θ (fun j k : ↥(D 1) => k = fD j) φ :=
      largeEvenMarking_mono (fun lab R _ I F θ h => h.2.2) hmark
    exact kgFieldRestriction_of_oneMarking_congr eCD fC fD (fun x => by simp [fD]) hmark'

end CFSG.StandardType
