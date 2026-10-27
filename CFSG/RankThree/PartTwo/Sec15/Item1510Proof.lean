module

public import CFSG.RankThree.PartTwo.Sec15.Item1510ProofTools
public import CFSG.RankThree.PartTwo.Sec13.Item13Inputs
public import CFSG.RankThree.PartTwo.Sec14.Notation
import CFSG.RankThree.PartTwo.Sec15.Item1511Meta
import CFSG.RankThree.PartTwo.Sec15.Item1514Steps1515
import CFSG.RankThree.PartTwo.Sec14.Concl143Std
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner
import CFSG.RankThree.PartTwo.Sec14.Item145Bot
import CFSG.RankThree.PartTwo.Sec13.OmegaNonempty
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.Sec13.Item133
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.KFacts.KS14HJSignalizer
import CFSG.RankThree.PartTwo.Late.Transitivity
import CFSG.RankThree.Theta.PlaneConditionSolvability
import CFSG.RankThree.PartTwo.Source.SolvableNormalizedTwoCore
import CFSG.CharacterTheory.Semidihedral.OddFieldLift
import CFSG.LinearAlgebra.LinearGroups.CoordinateData
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
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSmallSourceLinear
import CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModelSelector
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
import CFSG.RankThree.PartTwo.KFacts.KS12MovesSL
import CFSG.RankThree.PartTwo.Sec4.Census.Interface46
import CFSG.Sporadic.Schreier.J4SProfileNode
import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec15.Proof1511 CFSG.RankThree.PartTwo.Sec15.Proof1510
open CFSG.Assembly.RankThreeEven (projSL projSU aschCore)

section Defs

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def All1510 (A : Subgroup G) : Prop :=
  ∀ (c' : G) (L' : Subgroup G) (hL' : L' ∈ lA A c'), Subgroup.zpowers c' ∈ omegaA A →
    letI := kerAO2_normal hL'.2.1
    Nonempty (↥(A ⊔ L') ⧸ kerAO2 A L' ≃* Multiplicative (ZMod 3) × projSL 3 (GaloisField 2 2))

theorem all1510_of_not {A : Subgroup G} (h : ¬ Item1510 A) : All1510 A := by
  intro c' L' hL' hc'
  by_contra hne
  exact h ⟨c', L', hL', hc', not_nonempty_iff.mp hne⟩

end Defs

@[expose] noncomputable def Step1510Plane : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → All1510 A →
      ∀ E : Subgroup G, E ≤ A → Nat.card E = 9 → ∀ e ∈ E, e ≠ 1 →
        Subgroup.zpowers e ∈ omegaA A →
          ⁅inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer (E : Set G)), A⁆ ≤
            inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({e} : Set G))

@[expose] noncomputable def Step1510Cent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → All1510 A →
      ∀ B : Subgroup G, IsHyperplane A B → c ∈ B →
        thetaAlpha 3 B ≠ thetaAlpha 3 (A ⊓ L) →
          Subgroup.centralizer (B : Set G) ≤ Subgroup.normalizer (A : Set G) ⊔
            ⁅CFSG.Open.pCoreOf 2 L ⊓ Subgroup.centralizer (B : Set G), A⁆

@[expose] noncomputable def Step1510PGL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → All1510 A →
      ∀ B : Subgroup G, IsHyperplane A B → c ∈ B →
        thetaAlpha 3 B ≠ thetaAlpha 3 (A ⊓ L) →
        ∀ P : Subgroup G,
          CFSG.ABGLocalTools.IsSylowOf 3 P (Subgroup.centralizer (B : Set G)) →
          A ≤ P → A ≠ omegaOneThree P →
            Subgroup.normalizer (B : Set G) ⊓ Subgroup.normalizer (P : Set G) ≤
              Subgroup.normalizer (A : Set G)

section Proof

variable {G : Type} [Group G] [Finite G]

namespace Proof1510

theorem facts_l34_of_quot {A L : Subgroup G} {c : G} (hD : Sec13Data G A c L)
    (hq : letI := kerAO2_normal hD.le_normalizer
      Nonempty (↥(A ⊔ L) ⧸ kerAO2 A L ≃*
        Multiplicative (ZMod 3) × projSL 3 (GaloisField 2 2))) :
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* projSL 3 (GaloisField 2 2)) ∧
      Nat.card (A ⊓ L : Subgroup G) = 9 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := (isPerfect_center_projSL 2 2 (by norm_num) (by norm_num)).1
  have := Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field (GaloisField 2 2)
  exact facts_of_quot hD hq

theorem false_of_prod_of_l34 {A L : Subgroup G} {c : G} (hD : Sec13Data G A c L)
    (χ : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* projSL 3 (GaloisField 2 2)) {S : Type*} [Group S]
    (hS : Group.IsPerfect S) (hZ : Subgroup.center S = ⊥) (hcard : Nat.card S ≠ 20160)
    (φ : lBarA c L A ≃* Multiplicative (ZMod 3) × S) : False := by
  obtain ⟨-, -, -, ⟨ψ⟩⟩ := facts_of_prod hD hS hZ φ
  have h := Nat.card_congr (ψ.symm.trans χ).toEquiv
  rw [KFacts.KS14.card_projSL_three_four] at h
  exact hcard h


theorem false_of_prod_cases_of_l34 {A L : Subgroup G} {c : G} (hD : Sec13Data G A c L)
    (χ : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* projSL 3 (GaloisField 2 2))
    (h : Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × alternatingGroup (Fin 7)) ∨
      Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.M12) ∨
      Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.J2)) :
    False := by
  obtain ⟨-, ⟨hM12p, hM12z⟩, ⟨hJ2p, hJ2z⟩⟩ := sporadicModels131
  rcases h with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · obtain ⟨hS, hZ⟩ := isPerfect_center_alt7
    exact false_of_prod_of_l34 hD χ hS hZ
      (by rw [KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1]; norm_num) φ
  · exact false_of_prod_of_l34 hD χ hM12p hM12z (by rw [KFacts.KS14.card_nativeM12]; norm_num) φ
  · exact false_of_prod_of_l34 hD χ hJ2p hJ2z (by rw [KFacts.KS14.card_nativeJ2]; norm_num) φ

theorem key_of_all (h131 : Item131) (h133 : Item133) (hset : Item13SetupAt)
    {A L : Subgroup G} {c : G} (h : Sec15R G A c L) (hall : All1510 A) :
    (∀ d : G, Subgroup.zpowers d ∈ omegaA A → d ∉ L) ∧
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) ∧
      (∀ (d : G) (Ld : Subgroup G), Subgroup.zpowers d ∈ omegaA A → Ld ∈ lA A d →
        A ⊓ Ld = A ⊓ L) := by
  have hD := h.toSec13Data
  have hcL : c ∉ L := h.hypS.2.2 c h.zpowers_mem_omegaA L h.mem_lA
  obtain ⟨⟨χ⟩, h9⟩ := facts_l34_of_quot hD (hall c L h.mem_lA h.zpowers_mem_omegaA)
  obtain ⟨f, hfA, hfL, hfc⟩ := exists_mem_inf_not_mem_of_card_nine hD.card_zpowers h9
  have hirr : Sec21.IsIrreducibleOn
      (Sec4.autIn (L ⊓ Subgroup.normalizer (A : Set G)) (A ⊓ L)) := by
    rcases cases131 h131 sporadicModels131 slTwoCenter hD with ⟨-, -, -, hcase⟩ |
        ⟨-, -, he, -⟩ | ⟨-, hPGL, -⟩ | ⟨hcL', -⟩
    · exact Proof1514.isIrreducibleOn_of_cases131 hD hcL h9 hcase
    · exact (false_of_prod_cases_of_l34 hD χ (Or.inr he)).elim
    · exact (false_of_card_nine_of_isZ3PGLThreePi hD hcL h9 hPGL).elim
    · exact (hcL hcL').elim
  rcases h133 G A c L hD h.hypS_or_hypT with hWH | ⟨-, he7, -⟩ |
      ⟨-, hWD3, -, -, -, hΩ3, -, -, -⟩ | hPGL | he12 | heJ
  ·
    have hΩ1 : ∀ d : G, Subgroup.zpowers d ∈ omegaA A →
        Subgroup.zpowers d = Subgroup.zpowers c := by
      intro d hd
      obtain ⟨Ld, hLd⟩ := hset G h.toPartTwoStanding h.partTwoS_eq A h.mem_partTwoF
        h.not_mem_partTwoT d hd
      have hDd := (sec15R_point h hd hLd).toSec13Data
      obtain ⟨⟨χd⟩, h9d⟩ := facts_l34_of_quot hDd (hall d Ld hLd hd)
      have hcLd : d ∉ Ld := h.hypS.2.2 d hd Ld hLd
      rcases h133 G A d Ld hDd h.hypS_or_hypT with hWd | ⟨-, he7d, -⟩ |
          ⟨-, -, -, -, -, hΩd, -, -, -⟩ | hPGLd | he12d | heJd
      · exact zpowers_eq_of_le_normalizer hD hcL h9 hirr hDd.mem_A hDd.card_zpowers
          (inf_le_right.trans hWd)
      · exact (false_of_prod_cases_of_l34 hDd χd (Or.inl he7d)).elim
      · have hc' := h.zpowers_mem_omegaA
        rw [hΩd] at hc'
        obtain ⟨w, hw, hcw⟩ := hc'
        exact eq_of_eq_map_conj hcw (hWH hw)
      · exact (false_of_card_nine_of_isZ3PGLThreePi hDd hcLd h9d hPGLd).elim
      · exact (false_of_prod_cases_of_l34 hDd χd (Or.inr (Or.inl he12d))).elim
      · exact (false_of_prod_cases_of_l34 hDd χd (Or.inr (Or.inr heJd))).elim
    refine ⟨fun d hd hdL => ?_, fun w hw => ?_, fun d Ld hd hLd => ?_⟩
    · have hzd := hΩ1 d hd
      apply hcL
      have hcd : c ∈ Subgroup.zpowers d := hzd ▸ Subgroup.mem_zpowers c
      exact (Subgroup.zpowers_le.mpr hdL) hcd
    · have hwL : w ∈ Subgroup.normalizer (L : Set G) :=
        normalizer_inf_le_of_mem hD.mem_thetaComponentsAt hD.le_normalizer
          hD.sectionCentralizer_eq hfA hfL hfc ⟨hWH hw, hw⟩
      exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hw, hwL⟩
    · have hLd' : Ld ∈ lA A c := lA_eq_of_zpowers_eq (hΩ1 d hd) ▸ hLd
      rw [eq_of_mem_lA_of_mem hD.mem_thetaComponentsAt hLd' hfA hfL hfc]
  · exact (false_of_prod_cases_of_l34 hD χ (Or.inl he7)).elim
  ·
    refine ⟨fun d hd hdL => ?_, hWD3, fun d Ld hd hLd => ?_⟩
    · have hdA : d ∈ A := (zpowers_mem_omegaA_iff.mp hd).1
      rw [hΩ3] at hd
      obtain ⟨w, hw, hdw⟩ := hd
      have h1 : (Subgroup.zpowers d).map (MulAut.conj w⁻¹).toMonoidHom =
          Subgroup.zpowers c := by
        rw [hdw, Late.map_conj_map_conj, inv_mul_cancel, Late.map_conj_one]
      have h2 : (A ⊓ L).map (MulAut.conj w⁻¹).toMonoidHom = A ⊓ L :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (inv_mem (hWD3 hw))
      have h3 : Subgroup.zpowers c ≤ A ⊓ L := by
        rw [← h1, ← h2]
        exact Subgroup.map_mono (le_inf (Subgroup.zpowers_le.mpr hdA)
          (Subgroup.zpowers_le.mpr hdL))
      exact hcL (h3 (Subgroup.mem_zpowers c)).2
    · rw [hΩ3] at hd
      obtain ⟨w, hw, hdw⟩ := hd
      have hLdeq := eq_map_conj_of_mem_lA hD hfA hfL hfc hw hdw hLd
      have h2 : (A ⊓ L).map (MulAut.conj w).toMonoidHom = A ⊓ L :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hWD3 hw)
      rw [hLdeq, ← h2, Subgroup.map_inf _ _ _ (MulAut.conj w).injective, map_conj_eq_self hw]
  · exact (false_of_card_nine_of_isZ3PGLThreePi hD hcL h9 hPGL).elim
  · exact (false_of_prod_cases_of_l34 hD χ (Or.inr (Or.inl he12))).elim
  · exact (false_of_prod_cases_of_l34 hD χ (Or.inr (Or.inr heJ))).elim

omit [Finite G]
  in
theorem exists_isSylowOf_le {A B : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hBA : B ≤ A) :
    ∃ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 P (Subgroup.centralizer (B : Set G)) ∧
      A ≤ P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set CB := Subgroup.centralizer (B : Set G) with hCB
  have hAC : A ≤ CB := fun y hy =>
    Subgroup.mem_centralizer_iff.mpr fun z hz =>
      congrArg Subtype.val (hA.1.is_comm.comm ⟨z, hBA hz⟩ ⟨y, hy⟩)
  have hA3 : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hA.2 g g.2)⟩
  obtain ⟨P, hAP⟩ : ∃ P : Sylow 3 ↥CB, A.subgroupOf CB ≤ P :=
    (hA3.comap_subtype (K := CB)).exists_le_sylow
  refine ⟨(P : Subgroup ↥CB).map CB.subtype, ⟨P, rfl⟩, fun y hy => ?_⟩
  exact ⟨⟨y, hAC hy⟩, hAP (Subgroup.mem_subgroupOf.mpr hy), rfl⟩

end Proof1510

open Proof1510


theorem rank3II_15_10_of (h131 : Item131) (h133 : Item133) (hset : Item13SetupAt)
    (hplane : Step1510Plane) (hcent : Step1510Cent) (hpgl : Step1510PGL)
    {A L : Subgroup G} {c : G} (h : Sec15R G A c L) : Item1510 A := by
  by_contra hcon
  have hall : All1510 A := all1510_of_not hcon
  have hD := h.toSec13Data
  have hA := hD.isElemAbelian
  have h27 := hD.card_eq
  obtain ⟨-, h9⟩ := facts_l34_of_quot hD (hall c L h.mem_lA h.zpowers_mem_omegaA)
  obtain ⟨hΩL, hWD, hDd⟩ := key_of_all h131 h133 hset h hall
  set D := A ⊓ L with hDdef
  set α := thetaAlpha 3 D with hαdef
  have hDA : D ≤ A := inf_le_left
  have hPC : ∀ E : Subgroup G, E ≤ A → Nat.card E = 9 → ∀ e ∈ E, e ≠ 1 →
      ⁅inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer (E : Set G)), A⁆ ≤
        inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({e} : Set G)) := by
    intro E hEA hE9 e heE he1
    by_cases heΩ : Subgroup.zpowers e ∈ omegaA A
    · exact hplane G A c L h hall E hEA hE9 e heE he1 heΩ
    · exact commutator_theta_le_of_starConditionAt h.isE27' (hEA heE) he1
        (starConditionAt_of_not_mem_omegaA hA (hEA heE) he1 heΩ)
        ⟨hEA, by rw [h27, hE9]⟩ heE
  have h421 := fun (B : Subgroup G) (hBA : B ≤ A) (hB9 : Nat.card B = 9) (D' : Subgroup G)
      (hD'A : D' ≤ A) (hD'9 : Nat.card D' = 9) =>
    CFSG.RankThree.Theta.part_two_plane_condition_solvability_and_comparison A hA h27 hPC hBA
      hB9 hD'A hD'9
  obtain ⟨hαs, hα3, -⟩ := h421 D hDA h9 D hDA h9
  have hpt : ∀ B : Subgroup G, B ≤ A → Nat.card B = 9 → ∀ D' : Subgroup G, D' ≤ A →
      Nat.card D' = 9 → ¬ thetaAlpha 3 D' ≤ thetaAlpha 3 B →
        ∃ d ∈ B, d ∉ D' ∧ Subgroup.zpowers d ∈ omegaA A := by
    intro B hBA hB9 D' hD'A hD'9 hnle
    rcases (h421 D' hD'A hD'9 B hBA hB9).2.2 with hle | ⟨d, hdB, hdD, hstar⟩
    · exact absurd hle hnle
    · have hd1 : d ≠ 1 := fun h1 => hdD (h1 ▸ D'.one_mem)
      exact ⟨d, hdB, hdD, zpowers_mem_omegaA_iff.mpr
        ⟨hBA hdB, card_zpowers_eq_three hA (hBA hdB) hd1, hstar⟩⟩
  have hle : ∀ B : Subgroup G, B ≤ A → Nat.card B = 9 → thetaAlpha 3 B ≤ α := by
    intro B hBA hB9
    by_contra hnle
    obtain ⟨d, hdD, -, hdΩ⟩ := hpt D hDA h9 B hBA hB9 hnle
    exact hΩL d hdΩ hdD.2
  have hWα : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (α : Set G) :=
    hWD.trans (normalizer_le_normalizer_thetaAlpha D)
  have hNB : ∀ B : Subgroup G, B ≤ A → Nat.card B = 9 →
      Subgroup.normalizer (B : Set G) ≤ Subgroup.normalizer (α : Set G) := by
    intro B hBA hB9
    by_cases heq : thetaAlpha 3 B = α
    · rw [← heq]
      exact normalizer_le_normalizer_thetaAlpha B
    · have hnle : ¬ α ≤ thetaAlpha 3 B := fun h1 => heq (le_antisymm (hle B hBA hB9) h1)
      obtain ⟨d, hdB, -, hdΩ⟩ := hpt B hBA hB9 D hDA h9 hnle
      obtain ⟨Ld, hLd⟩ := hset G h.toPartTwoStanding h.partTwoS_eq A h.mem_partTwoF
        h.not_mem_partTwoT d hdΩ
      have hRd : Sec15R G A d Ld := sec15R_point h hdΩ hLd
      have hDd' : A ⊓ Ld = D := hDd d Ld hdΩ hLd
      have hBh : IsHyperplane A B := ⟨hBA, by rw [h27, hB9]⟩
      have hne' : thetaAlpha 3 B ≠ thetaAlpha 3 (A ⊓ Ld) := by
        rw [hDd']
        exact heq
      have hC : Subgroup.centralizer (B : Set G) ≤ Subgroup.normalizer (A : Set G) ⊔ α := by
        obtain ⟨⟨χd⟩, -⟩ := facts_l34_of_quot hRd.toSec13Data (hall d Ld hLd hdΩ)
        have h3d : 3 ∣ Nat.card Ld := three_dvd_card_of_thetaQuot χd
          (by rw [KFacts.KS14.card_projSL_three_four]; norm_num)
        have hLdN := centralizer_le_normalizer_of_three_dvd hRd.toSec14Std h3d
        refine (hcent G A d Ld hRd hall B hBh hdB hne').trans (sup_le_sup_left ?_ _)
        exact (commutator_pCoreOf_inf_le_thetaAlpha hdB hLdN
          fun e he he1 => hPC B hBA hB9 e he he1).trans (hle B hBA hB9)
      obtain ⟨P, hP, hAP⟩ := exists_isSylowOf_le hA hBA
      have hNP : Subgroup.normalizer (B : Set G) ⊓ Subgroup.normalizer (P : Set G) ≤
          Subgroup.normalizer (A : Set G) := by
        by_cases hAP' : A = omegaOneThree P
        · exact inf_le_right.trans (normalizer_le_of_eq_omegaOneThree hAP')
        · exact hpgl G A d Ld hRd hall B hBh hdB hne' P hP hAP hAP'
      calc Subgroup.normalizer (B : Set G)
          ≤ Subgroup.centralizer (B : Set G) ⊔
              (Subgroup.normalizer (B : Set G) ⊓ Subgroup.normalizer (P : Set G)) :=
            normalizer_le_sup_of_isSylowOf hP
        _ ≤ (Subgroup.normalizer (A : Set G) ⊔ α) ⊔ Subgroup.normalizer (A : Set G) :=
            sup_le_sup hC hNP
        _ ≤ Subgroup.normalizer (α : Set G) :=
            sup_le (sup_le hWα Subgroup.le_normalizer) hWα
  have hΓ : aschCore 2 3 A ≤ Subgroup.normalizer (α : Set G) :=
    aschCore_le_normalizer_of h27 hNB hWα
  have hα1 : α = ⊥ := by
    by_contra hne
    have h3 : ¬ 3 ∣ Nat.card α := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hα3
    exact h.not_mem_partTwoT
      (Source.rank3II_6_2 h.charTwoType h.localRank_lt hD.mem_partTwoE hne hαs h3 hΓ).2
  have hS : A ∈ partTwoS G := mem_partTwoS_of_thetaAlpha_eq_bot h.mem_partTwoF hA h27
    (fun B hBA hB9 => eq_bot_iff.mpr ((hle B hBA hB9).trans hα1.le))
  rw [h.partTwoS_eq] at hS
  exact hS

end Proof

theorem item1510R_of
    (h131 : Item131) (h133 : Item133) (hset : Item13SetupAt)
    (hplane : Step1510Plane) (hcent : Step1510Cent) (hpgl : Step1510PGL) : Item1510R :=
  fun _ _ _ _ _ _ h => rank3II_15_10_of h131 h133 hset hplane hcent hpgl h

end CFSG.RankThree.PartTwo.Sec15
