module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusCuts
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelCoordinates
public import CFSG.Open.StatedDefs

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllResidSL
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusData
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusResGroup
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusPlane
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockLinData
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Levi
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOrdNatural.PCoreOmegaMinus
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CanonicalLocalObstruction
import CFSG.Adapters.SpecialLinearPerfect
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
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
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailPolar
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailWeylLift
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
import CFSG.LocalAnalysis.AGLEmbedding.IIIaResidualDefs
import CFSG.LocalAnalysis.AGLEmbedding.J3MSideDefs
import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusBlocks
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherBorelOvergroups
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelBorel
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
import CFSG.Quasithin.Background.A1cModuleCoprime
import CFSG.Quasithin.Background.A3Components
import CFSG.Quasithin.Background.A3Structure312
import CFSG.Quasithin.Background.OrderingMax
import CFSG.Quasithin.Vol2.Ch1Local
import CFSG.Sporadic.J4Base
import Certificates.Certificate8026Base
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.AGLEmbedding.LeviBlock
open scoped commutatorElement

private theorem nonempty_bar2_hinf_equiv_of_leviHom_of_comm {G A : Type} [Group G] [Finite G]
    [Group A] (P : Subgroup G) (β : ↥P →* A) (hker : IsPGroup 2 ↥β.ker) (S C : Subgroup A)
    (hSR : S ≤ β.range) (hcomm : ⁅β.range, β.range⁆ ≤ C) (hCS : ⁅C, C⁆ ≤ S)
    (hperf : ⁅S, S⁆ = S) (hO2 : CFSG.pCore 2 ↥S = ⊥) : Nonempty (Bar2 (Hinf P) ≃* ↥S) := by
  set P₁ : Subgroup G := (C.comap β).map P.subtype
  have hP₁P : P₁ ≤ P := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  let β₁ : ↥P₁ →* A := β.comp (Subgroup.inclusion hP₁P)
  have hR₁C : β₁.range ≤ C := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨y, hy, hyw⟩ := w.2
    have hw : Subgroup.inclusion hP₁P w = y := Subtype.ext hyw.symm
    change β (Subgroup.inclusion hP₁P w) ∈ C
    rw [hw]
    exact hy
  have hSC : S ≤ C := calc
    S = ⁅S, S⁆ := hperf.symm
    _ ≤ ⁅β.range, β.range⁆ := Subgroup.commutator_mono hSR hSR
    _ ≤ C := hcomm
  have hSR₁ : S ≤ β₁.range := by
    intro s hs
    obtain ⟨y, hy⟩ := hSR hs
    have hyC : y ∈ C.comap β := by
      change β y ∈ C
      rw [hy]
      exact hSC hs
    exact ⟨⟨P.subtype y, y, hyC, rfl⟩, hy⟩
  have hker₁ : IsPGroup 2 ↥β₁.ker := by
    let κ : ↥β₁.ker →* ↥β.ker :=
      ((Subgroup.inclusion hP₁P).comp β₁.ker.subtype).codRestrict β.ker fun z => z.2
    refine hker.of_injective κ fun z₁ z₂ h => Subtype.ext (Subgroup.inclusion_injective hP₁P ?_)
    exact congrArg Subtype.val h
  obtain ⟨e⟩ := KTabD.nonempty_bar2_hinf_equiv_of_leviHom P₁ β₁ hker₁ S hSR₁
    ((Subgroup.commutator_mono hR₁C hR₁C).trans hCS) hperf hO2
  have hres : ∀ y ∈ CFSG.perfectResidual ↥P, β y ∈ C := by
    intro y hy
    have h1 : y ∈ ⁅(⊤ : Subgroup ↥P), (⊤ : Subgroup ↥P)⁆ := by
      have h := (iInf_le (fun n => derivedSeries ↥P n) 1) hy
      rwa [derivedSeries_one, commutator_def] at h
    apply hcomm
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator]
    exact ⟨y, h1, rfl⟩
  have hHP : Hinf P ≤ P₁ := by
    unfold Hinf CFSG.inSubgroup
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨y, hres y hy, rfl⟩
  have hEq : Hinf P₁ = Hinf P := le_antisymm
    (CFSG.RankThreeCoreUniqueness.Helpers.perfect_subgroup_le_perfectResidualOf _ P
      (CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidualOf_isPerfect P₁)
      ((Subgroup.map_subtype_le _).trans hP₁P))
    (CFSG.RankThreeCoreUniqueness.Helpers.perfect_subgroup_le_perfectResidualOf _ P₁
      (CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidualOf_isPerfect P) hHP)
  rw [hEq] at e
  exact ⟨e⟩

private theorem nonempty_bar2_hinf_equiv_of_leviHom_mulSingle_of_comm {G : Type} [Group G]
    [Finite G] {ι : Type} [DecidableEq ι] {M : ι → Type} [∀ i, Group (M i)] (P : Subgroup G)
    (β : ↥P →* ∀ i, M i) (hker : IsPGroup 2 ↥β.ker) (j₀ : ι) (B : ∀ i, Subgroup (M i))
    (hB : ∀ j, j ≠ j₀ → ⁅B j, B j⁆ = ⊥) (hSR : ∀ y ∈ B j₀, Pi.mulSingle j₀ y ∈ β.range)
    (hcomm : ⁅β.range, β.range⁆ ≤ Subgroup.pi Set.univ B) {T : Type} [Group T]
    (eS : ↥(B j₀) ≃* T) (hperf : Group.IsPerfect T) (hT : CFSG.pCore 2 T = ⊥) :
    Nonempty (Bar2 (Hinf P) ≃* T) := by
  let f : M j₀ →* (∀ i, M i) := MonoidHom.mulSingle M j₀
  let S : Subgroup (∀ i, M i) := (B j₀).map f
  let eS' : ↥S ≃* T := ((B j₀).equivMapOfInjective f (Pi.mulSingle_injective j₀)).symm.trans eS
  have : Group.IsPerfect T := hperf
  have : Group.IsPerfect ↥S :=
    Group.IsPerfect.ofSurjective (f := eS'.symm.toMonoidHom) eS'.symm.surjective
  have hSO2 : CFSG.pCore 2 ↥S = ⊥ := by
    have hmap : (CFSG.pCore 2 ↥S).map eS'.toMonoidHom = ⊥ := by
      rw [CFSG.pCore_map_iso 2 eS']
      exact hT
    exact (Subgroup.map_eq_bot_iff_of_injective _ eS'.injective).mp hmap
  have hCS : ⁅Subgroup.pi Set.univ B, Subgroup.pi Set.univ B⁆ ≤ S := by
    intro x hx
    have hx' := (Subgroup.mem_pi _).mp (Subgroup.commutator_pi_pi_le B B hx)
    refine ⟨x j₀, Subgroup.commutator_le_self _ (hx' j₀ (Set.mem_univ _)), funext fun j => ?_⟩
    by_cases hj : j = j₀
    · rw [hj]
      exact Pi.mulSingle_eq_same j₀ (x j₀)
    · have hxj := hx' j (Set.mem_univ _)
      rw [hB j hj, Subgroup.mem_bot] at hxj
      rw [hxj]
      exact Pi.mulSingle_eq_of_ne hj (x j₀)
  obtain ⟨e⟩ := nonempty_bar2_hinf_equiv_of_leviHom_of_comm P β hker S (Subgroup.pi Set.univ B)
    (by rintro _ ⟨y, hy, rfl⟩; exact hSR y hy) hcomm hCS (Subgroup.commutator_eq_self (H := S))
    hSO2
  exact ⟨e.trans eS'⟩

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [CharP K 2] in
private theorem finite_orthElementaryGroup_three (b c : K) :
    Finite ↥(orthElementaryGroup (quadTail 3 (minusTailForm K b c))) :=
  have : Finite (((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K))) := finite_orthLinearEquiv
  Subtype.finite

omit [Finite K] [CharP K 2] in
private theorem orthCuts_zero_two : OrthCuts 3 ![0, 2] where
  mono := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  zero := rfl
  last := by decide

omit [Finite K] [CharP K 2] in
private theorem orthCuts_zero_three : OrthCuts 3 ![0, 3] where
  mono := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  zero := rfl
  last := by decide

private theorem commutator_orthResDer_zero {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ⁅orthResDer K b c 0, orthResDer K b c 0⁆ = ⊥ := by
  let e := orthMinusCommutatorCongr (minusTailZeroIsometry (b := b) (c := c))
  have hab : ∀ x y : ↥(orthResDer K b c 0), x * y = y * x := fun x y => e.injective (by
    rw [map_mul, map_mul]
    exact Subtype.ext (commute_of_mem_commutator_minusTailForm hirr (e x).2 (e y).2))
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact congrArg Subtype.val (hab ⟨y, hy⟩ ⟨x, hx⟩)

omit [Finite K] [CharP K 2] in
private theorem isPerfect_of_isSimpleGroup {T : Type} [Group T] (hs : IsSimpleGroup T)
    (hna : ∃ x y : T, x * y ≠ y * x) : Group.IsPerfect T := by
  refine ⟨(hs.eq_bot_or_eq_top_of_normal (commutator T)).resolve_left fun h => ?_⟩
  obtain ⟨x, y, hxy⟩ := hna
  have hc : ⁅x, y⁆ ∈ commutator T := by
    rw [commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
  rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
  exact hxy hc

theorem nonempty_bar2_hinf_orthParab_minus_three {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nonempty (Bar2 (Hinf (orthParab 3 (minusTailForm K b c) ![0, 3])) ≃*
      Matrix.SpecialLinearGroup (Fin 3) K) := by
  have := finite_orthElementaryGroup_three b c
  have hE := commutator_orthogonalGroup_quadTail_minus (K := K) (b := b) (c := c) (le_refl 3) hirr
  have hlen : (![0, 3] : Fin 2 → ℕ) (Fin.succ 0) - ![0, 3] (Fin.castSucc 0) = 3 := by decide
  refine nonempty_bar2_hinf_equiv_of_leviHom_mulSingle_of_comm _
    (orthLeviHom b c orthCuts_zero_three) (isPGroup_ker_orthLeviHom orthCuts_zero_three)
    (Sum.inl 0) (orthLeviBlock K 3 ![0, 3] b c) ?_ (fun y hy => ?_)
    (commutator_range_orthLeviHom_le orthCuts_zero_three)
    ((slEquivToGLRange _).symm.trans
      (MulEquiv.cast (M := fun m : ℕ => Matrix.SpecialLinearGroup (Fin m) K) hlen))
    (CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le le_rfl)
    (pCore_specialLinearGroup_eq_bot 3)
  · rintro (l | u) hj
    · exact absurd (congrArg Sum.inl (Subsingleton.elim l 0)) hj
    · exact commutator_orthResDer_zero hirr
  · exact pi_orthLeviBlock_le_range orthCuts_zero_three (le_refl 3) hE
      ((Subgroup.mulSingle_mem_pi _ _).mpr fun _ => hy)

theorem nonempty_bar2_hinf_orthParab_minus_two {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hK : 4 ≤ Nat.card K) :
    Nonempty (Bar2 (Hinf (orthParab 3 (minusTailForm K b c) ![0, 2])) ≃*
      Matrix.SpecialLinearGroup (Fin 2) K × ↥(StatedOmega (StatedQuadMinus 2 K b c))) := by
  have := finite_orthElementaryGroup_three b c
  have hE := commutator_orthogonalGroup_quadTail_minus (K := K) (b := b) (c := c) (le_refl 3) hirr
  have hlen : (![0, 2] : Fin 2 → ℕ) (Fin.succ 0) - ![0, 2] (Fin.castSucc 0) = 2 := by decide
  have hperf : Group.IsPerfect ↥(StatedOmega (StatedQuadMinus 2 K b c)) := by
    obtain ⟨f, hKf⟩ : ∃ f, Nat.card K = 2 ^ f := by
      have := Fintype.ofFinite K
      obtain ⟨n, -, hn⟩ := FiniteField.card K 2
      exact ⟨n, by rw [Nat.card_eq_fintype_card, hn]⟩
    obtain ⟨hs, hna, -⟩ := orthResDer_facts (K := K) (b := b) (c := c) (m := 1) hKf le_rfl hirr
    have := isPerfect_of_isSimpleGroup hs hna
    exact Group.IsPerfect.ofSurjective
      (f := (orthResDerEquivStatedOmega (b := b) (c := c) 1).toMonoidHom)
      (orthResDerEquivStatedOmega (b := b) (c := c) 1).surjective
  refine nonempty_bar2_hinf_equiv_of_leviHom_mulSingle_two _
    (orthLeviHom b c orthCuts_zero_two) (isPGroup_ker_orthLeviHom orthCuts_zero_two)
    (j₀ := Sum.inl 0) (j₁ := Sum.inr ()) Sum.inl_ne_inr (orthLeviBlock K 3 ![0, 2] b c) ?_
    (pi_orthLeviBlock_le_range orthCuts_zero_two (le_refl 3) hE)
    (commutator_range_orthLeviHom_le orthCuts_zero_two)
    (T₀ := Matrix.SpecialLinearGroup (Fin 2) K) (T₁ := ↥(StatedOmega (StatedQuadMinus 2 K b c)))
    ((slEquivToGLRange _).symm.trans
      (MulEquiv.cast (M := fun m : ℕ => Matrix.SpecialLinearGroup (Fin m) K) hlen))
    (orthResDerEquivStatedOmega (b := b) (c := c) 1)
    (CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK) hperf
    (pCore_specialLinearGroup_eq_bot 2)
    (KOrdNat.pCore_statedOmega_minus_eq_bot (K := K) 2 (m := 2) le_rfl hirr)
  rintro (l | u) h0 h1
  · exact absurd (congrArg Sum.inl (Subsingleton.elim l 0)) h0
  · exact absurd rfl h1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
