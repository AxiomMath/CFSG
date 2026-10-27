module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
public import CFSG.Open.StatedDefs

import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusData
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusResGroup
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.OmegaMinusFlag
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.LeviTools
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Bar2Map
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOrdNatural.PCoreOmegaMinus
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary
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
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
import CFSG.ClassicalGroups.Orthogonal.RootGroupFixedCard
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

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD

open CFSG.Open
open CFSG.AGLEmbedding.LeviBlock
open CFSG.ClassicalGroups.Orthogonal
open CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open scoped commutatorElement

private theorem orthCuts_zero_one_Q04 {r : ℕ} (hr : 1 ≤ r) : OrthCuts r ![0, 1] where
  mono := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all <;> decide
  zero := rfl
  last := by
    rw [show (![0, 1] : Fin 2 → ℕ) (Fin.last 1) = 1 by decide]
    exact hr

private theorem isPerfect_of_simple_noncomm_Q04 {T : Type} [Group T] (hs : IsSimpleGroup T)
    (hna : ∃ x y : T, x * y ≠ y * x) : Group.IsPerfect T := by
  refine ⟨?_⟩
  rcases hs.eq_bot_or_eq_top_of_normal (commutator T) with h | h
  · obtain ⟨a, b, hab⟩ := hna
    have hc : ⁅a, b⁆ ∈ commutator T := by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    exact absurd hc hab
  · exact h

private instance finite_orthElementaryGroup_quadTail_Q04 {K : Type} [Field K] [Finite K] {r : ℕ}
    {b c : K} : Finite ↥(orthElementaryGroup (quadTail r (minusTailForm K b c))) := by
  haveI : Finite (((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin r ⊕ Fin r → K) × (Fin 2 → K))) :=
    finite_orthLinearEquiv (K := K) (M := ((Fin r ⊕ Fin r → K) × (Fin 2 → K)))
  exact Finite.of_injective (Subtype.val) Subtype.val_injective

private theorem commutator_orthogonalGroup_quadTail_minus_of_one_le_Q04 {K : Type} [Field K]
    [Finite K] [CharP K 2] {b c : K} {r : ℕ} (hr : 1 ≤ r)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ⁅TauCeti.QuadraticMap.orthogonalGroup (quadTail r (minusTailForm K b c)),
      TauCeti.QuadraticMap.orthogonalGroup (quadTail r (minusTailForm K b c))⁆ =
        orthElementaryGroup (quadTail r (minusTailForm K b c)) := by
  let ψ : (quadTail r (minusTailForm K b c)).IsometryEquiv (quadMinus (r + 1) K b c) :=
    minusTailIsometry (r + 1) K b c
  apply Subgroup.map_injective (f := (LinearEquiv.autCongr ψ.toLinearEquiv).toMonoidHom)
    (LinearEquiv.autCongr ψ.toLinearEquiv).injective
  rw [orthMinus_map_autCongr_commutator ψ,
    commutator_orthogonalGroup_quadMinus_of_two_le (n := r + 1) (by omega) hirr]
  exact (CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry.elementaryGroup_map ψ).symm

private theorem nonempty_bar2_hinf_orthParab_one_Q04 {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : ℕ) :
    Nonempty (Bar2 (Hinf (orthParab (k + 2) (minusTailForm K b c) ![0, 1])) ≃*
      ↥(orthResDer K b c (k + 1))) := by
  let hd : OrthCuts (k + 2) ![0, 1] := orthCuts_zero_one_Q04 (by omega)
  let P := orthParab (k + 2) (minusTailForm K b c) ![0, 1]
  let β : ↥P →* ∀ j, orthLeviGroup K (k + 2) ![0, 1] j :=
    orthLeviHom (b := b) (c := c) hd
  let B := orthLeviBlock K (k + 2) ![0, 1] b c
  let T := ↥(orthResDer K b c (k + 1))
  have hE := commutator_orthogonalGroup_quadTail_minus_of_one_le_Q04 (K := K) (b := b) (c := c)
    (r := k + 2) (by omega) hirr
  have hker : IsPGroup 2 ↥β.ker := isPGroup_ker_orthLeviHom (b := b) (c := c) hd
  have hB : ∀ j, j ≠ Sum.inr () → B j = ⊥ := by
    intro j hj
    rcases j with l | u
    · obtain rfl : l = 0 := Subsingleton.elim l 0
      change orthLeviBlock K (k + 2) ![0, 1] b c (Sum.inl 0) = ⊥
      rw [orthLeviBlock]
      exact range_toGL_eq_bot_of_eq_one (K := K) (by decide)
    · exact absurd rfl hj
  have hSR : ∀ y ∈ B (Sum.inr ()), Pi.mulSingle (Sum.inr ()) y ∈ β.range := by
    intro y hy
    refine ⟨orthLeviResElt (b := b) (c := c) hd hE ⟨y, hy⟩, ?_⟩
    exact orthLeviHom_orthLeviResElt (b := b) (c := c) hd hE ⟨y, hy⟩
  have hcomm : ⁅β.range, β.range⁆ ≤ Subgroup.pi Set.univ B :=
    commutator_range_orthLeviHom_le (b := b) (c := c) hd
  have hperf : Group.IsPerfect T := by
    letI : Fintype K := Fintype.ofFinite K
    obtain ⟨f, _, hKf⟩ := FiniteField.card K 2
    have hK : Nat.card K = 2 ^ (f : ℕ) := by
      rw [Nat.card_eq_fintype_card, hKf]
    obtain ⟨hsimple, hna, -⟩ := orthResDer_facts (K := K) (b := b) (c := c) (m := k + 1)
      hK (by omega) hirr
    exact isPerfect_of_simple_noncomm_Q04 hsimple hna
  have hT : CFSG.pCore 2 T = ⊥ := by
    let e := orthResDerEquivStatedOmega (b := b) (c := c) (k + 1)
    have hmap : (CFSG.pCore 2 T).map e.toMonoidHom = ⊥ := by
      rw [CFSG.pCore_map_iso 2 e,
        CFSG.LocalAnalysis.UniquenessCase.UC22.KOrdNat.pCore_statedOmega_minus_eq_bot (K := K)
          (p := 2) (m := k + 2) (by omega) hirr]
    exact (Subgroup.map_eq_bot_iff_of_injective (CFSG.pCore 2 T) e.injective).mp hmap
  exact nonempty_bar2_hinf_equiv_of_leviHom_mulSingle P β hker (Sum.inr ()) B hB hSR hcomm
    (T := T) (MulEquiv.refl T) hperf hT

theorem nonempty_bar2_hinf_lineStab_statedOmegaMinus {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : ℕ) :
    Nonempty (Bar2 (Hinf (lineStab (StatedOmega (StatedQuadMinus (k + 3) K b c))
      (Pi.single (Sum.inl ⟨0, by omega⟩) 1))) ≃*
        ↥(StatedOmega (StatedQuadMinus (k + 2) K b c))) := by
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_lineStab_map_eq_orthParab hirr k
  obtain ⟨e1⟩ := nonempty_bar2_hinf_map φ
    (lineStab (StatedOmega (StatedQuadMinus (k + 3) K b c))
      (Pi.single (Sum.inl ⟨0, by omega⟩) 1))
  obtain ⟨e2⟩ := nonempty_bar2_hinf_orthParab_one_Q04 hirr k
  rw [hφ] at e1
  exact ⟨e1.trans (e2.trans (orthResDerEquivStatedOmega (b := b) (c := c) (k + 1)))⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD
