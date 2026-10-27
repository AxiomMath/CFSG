module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S22c
public import CFSG.Quasithin.Background.A1bKrullSchmidt
import all CFSG.Quasithin.Background.A1bKrullSchmidt
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ya
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveQuot
import CFSG.Mathlib.GroupTheory.PermCommute
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
import CFSG.ClassicalInvolution.QuaternionStructure
import CFSG.ClassicalInvolution.WeakCT.Main
import CFSG.GH74.GLS.Defs
import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Closed
import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Statements
import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Defs
import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Ext
import CFSG.GH74.GLS.Stage2.Final.LayerFDerive
import CFSG.LieType.CurtisTits.Adjoint
import CFSG.LieType.Ree.LargeReeEightTorus
import CFSG.LieType.Ree.LargeReeInvolutionTwoCentralizers
import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenE6
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenTriality
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddE6
import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
import CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModelCases
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBasic
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
import CFSG.LocalAnalysis.SeitzReduction.CrossCharInputs
import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviPerp
import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2PositionWork
import CFSG.LocalAnalysis.SeitzReduction.E8PilotSwapLift
import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphE6
import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphTwistedXi
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassical
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatSporadic
import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndField
import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourFix
import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourLift
import CFSG.LocalAnalysis.SeitzReduction.F4PilotInnerField
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWSmall
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWSylow
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwapFactorNormalGraph
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTwistedFusion
import CFSG.LocalAnalysis.SeitzReduction.RankOneBranches
import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2TwoFixedA5
import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarDef
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotAlignImagesSwap
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUniqueTypeGraph
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsHyp
import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl
import CFSG.RankThree.Chevalley.SteinbergCFEvenF4PointwiseInner
import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext (IsInternalDirect)
open CFSG.Quasithin (IsIndecomposableGroup IsIndexedDirectProduct)
open CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.Sigma3 (Sigma3Dec.isIndecomposableGroup_of_mulEquiv
  Sigma3Dec.center_eq_bot_of_mulEquiv)

namespace P22w

section Indexed

variable {Y : Type} [Group Y] [Finite Y] {ι κ : Type} {Xs : ι → Subgroup Y} {Ys : κ → Subgroup Y}

theorem exists_le_of_isIndexedDirectProduct (hX : IsIndexedDirectProduct Xs) (hY : IsIndexedDirectProduct Ys)
    (hind : ∀ i, IsIndecomposableGroup ↥(Xs i)) (hZ : center Y = ⊥) (i : ι) : ∃ k, Xs i ≤ Ys k := by
  have hmap : (Xs i).map (MulEquiv.refl Y).toMonoidHom = Xs i := by
    ext x
    simp
  have key : ∀ k, Xs i ⊓ CFSG.Quasithin.A1b.restProd Ys k = ⊥ ∨ Xs i ⊓ Ys k = ⊥ := fun k => by
    have := CFSG.Quasithin.A1b.aut_disjoint_or (hX.normal i) (hX.normal_restProd i) (hX.inf_restProd i)
      (hX.sup_restProd i) (hind i) (hY.normal k) (hY.normal_restProd k) (hY.inf_restProd k) (hY.sup_restProd k)
      (MulEquiv.refl Y)
    rwa [hmap] at this
  have hne : Xs i ≠ ⊥ := (nontrivial_iff_ne_bot _).1 (hind i).1
  by_cases hex : ∃ k, Xs i ⊓ CFSG.Quasithin.A1b.restProd Ys k = ⊥
  · obtain ⟨k, hk⟩ := hex
    refine ⟨k, ?_⟩
    have h := hY.le_sup_center k (S := Xs i) fun l hlk x hx y hy =>
      commute_of_normal_of_disjoint _ _ (hX.normal i) (hY.normal l)
        ((disjoint_iff.2 hk).mono_right (IsIndexedDirectProduct.le_restProd hlk)) x y hx hy
    rwa [hZ, sup_bot_eq] at h
  · push Not at hex
    refine absurd (le_bot_iff.1 ?_) hne
    rw [← hZ]
    intro x hx
    exact hY.mem_center_of_commute fun l y hy => commute_of_normal_of_disjoint _ _ (hX.normal i)
      (hY.normal l) (disjoint_iff.2 ((key l).resolve_left (hex l))) x y hx hy

theorem exists_equiv_of_isIndexedDirectProduct (hX : IsIndexedDirectProduct Xs) (hY : IsIndexedDirectProduct Ys)
    (hindX : ∀ i, IsIndecomposableGroup ↥(Xs i)) (hindY : ∀ k, IsIndecomposableGroup ↥(Ys k))
    (hZ : center Y = ⊥) : ∃ σ : ι ≃ κ, ∀ i, Xs i = Ys (σ i) := by
  choose f hf using exists_le_of_isIndexedDirectProduct hX hY hindX hZ
  choose g hg using exists_le_of_isIndexedDirectProduct hY hX hindY hZ
  have hgf : ∀ i, g (f i) = i := fun i => by
    by_contra h
    exact (nontrivial_iff_ne_bot _).1 (hindX i).1
      ((hX.disjoint (Ne.symm h)).eq_bot_of_le ((hf i).trans (hg (f i))))
  have hfg : ∀ k, f (g k) = k := fun k => by
    by_contra h
    exact (nontrivial_iff_ne_bot _).1 (hindY k).1
      ((hY.disjoint (Ne.symm h)).eq_bot_of_le ((hg k).trans (hf (g k))))
  refine ⟨⟨f, g, hgf, hfg⟩, fun i => le_antisymm (hf i) ?_⟩
  have := hg (f i)
  rwa [hgf i] at this

end Indexed

section Internal

variable {X : Type} [Group X] {m : ℕ} {H : Subgroup X} {A : Fin m → Subgroup X}

theorem le_of_isInternalDirect (hA : IsInternalDirect H A) (i : Fin m) : A i ≤ H := by
  rw [← hA.1]
  exact le_iSup A i

theorem le_normalizer_of_isInternalDirect (hA : IsInternalDirect H A) (i : Fin m) :
    H ≤ normalizer (A i : Set X) := by
  rw [← hA.1]
  refine iSup_le fun k => ?_
  by_cases hk : k = i
  · subst hk
    exact le_normalizer
  · refine le_trans (fun y hy => ?_) (centralizer_le_normalizer _)
    rw [mem_centralizer_iff]
    intro x hx
    exact hA.2.1 i k (Ne.symm hk) x hx y hy

theorem isIndexedDirectProduct_subgroupOf (hA : IsInternalDirect H A) :
    IsIndexedDirectProduct fun i => (A i).subgroupOf H where
  normal i := (normal_subgroupOf_iff_le_normalizer (le_of_isInternalDirect hA i)).2
    (le_normalizer_of_isInternalDirect hA i)
  independent i := by
    rw [disjoint_iff, eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    have hle : (⨆ (j) (_ : j ≠ i), (A j).subgroupOf H) ≤ (⨆ (j) (_ : j ≠ i), A j).subgroupOf H :=
      iSup₂_le fun j hj => subgroupOf_mono H (le_iSup₂ (f := fun j (_ : j ≠ i) => A j) j hj)
    have hx : (x : X) ∈ A i ⊓ ⨆ (j) (_ : j ≠ i), A j := mem_inf.2 ⟨hx1, mem_subgroupOf.1 (hle hx2)⟩
    rw [disjoint_iff.1 (P22y.iSupIndep_of hA i), mem_bot] at hx
    exact mem_bot.2 (Subtype.ext hx)
  iSup_eq_top := by
    apply map_injective H.subtype_injective
    have h : ∀ i, ((A i).subgroupOf H).map H.subtype = A i := fun i =>
      map_subgroupOf_eq_of_le (le_of_isInternalDirect hA i)
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, range_subtype]
    simp only [h]
    exact hA.1

theorem center_eq_bot_of_isInternalDirect (hA : IsInternalDirect H A) (hZ : ∀ i, center ↥(A i) = ⊥) :
    center ↥H = ⊥ := by
  let e : (∀ i, ↥(A i)) ≃* ↥H :=
    (MonoidHom.ofInjective (P22y.piMul_injective hA)).trans (MulEquiv.subgroupCongr (P22y.piMul_range hA))
  have hc : center (∀ i, ↥(A i)) = ⊥ := by
    rw [Subgroup.center_pi, Subgroup.pi_eq_bot_iff]
    exact hZ
  refine Sigma3Dec.center_eq_bot_of_mulEquiv e.symm fun y hy => ?_
  have hy' : y ∈ center (∀ i, ↥(A i)) := mem_center_iff.2 fun z => (hy z).symm
  rwa [hc, mem_bot] at hy'

end Internal

theorem isIndecomposable_perm_five : IsIndecomposableGroup (Equiv.Perm (Fin 5)) := by
  refine ⟨inferInstance, fun B C hB hC hBC _ => ?_⟩
  by_contra hcon
  push Not at hcon
  have h5 : 5 ≤ Nat.card (Fin 5) := by simp
  have hB' := Equiv.Perm.alternatingGroup_le_of_normal (N := B) h5 ((nontrivial_iff_ne_bot B).2 hcon.1)
  have hC' := Equiv.Perm.alternatingGroup_le_of_normal (N := C) h5 ((nontrivial_iff_ne_bot C).2 hcon.2)
  have hA5 : alternatingGroup (Fin 5) ≠ ⊥ := (nontrivial_iff_ne_bot _).1 inferInstance
  refine hA5 (le_bot_iff.1 ?_)
  rw [← hBC]
  exact le_inf hB' hC'

theorem isIndecomposable_of_factorShape22 {Z : Type} [Group Z] [Finite Z] (h : FactorShape22 Z) :
    IsIndecomposableGroup Z := by
  rcases h with ⟨n, h⟩ | h | h
  · exact P22y.isIndecomposable_of_isL2Ev h
  · haveI := PartTwo.isSimpleGroup_of_isL3 h
    exact P22y.isIndecomposable_of_isSimpleGroup
  · obtain ⟨e⟩ := h
    exact Sigma3Dec.isIndecomposableGroup_of_mulEquiv e isIndecomposable_perm_five

theorem center_eq_bot_of_factorShape22 {Z : Type} [Group Z] [Finite Z] (h : FactorShape22 Z) :
    center Z = ⊥ := by
  rcases h with ⟨n, h⟩ | h | h
  · exact P22y.center_eq_bot_of_isL2Ev h
  · exact PartTwo.center_eq_bot_of_isL3 h
  · obtain ⟨e⟩ := h
    exact Sigma3Dec.center_eq_bot_of_mulEquiv e fun y hy =>
      CFSG.perm_eq_one_of_forall_commute (by simp) hy

end P22w

theorem uc22p22wg_remak {X : Type} [Group X] [Finite X] {H : Subgroup X} {m m' : ℕ}
    {A : Fin m → Subgroup X} {B : Fin m' → Subgroup X} (hA : IsInternalDirect H A) (hB : IsInternalDirect H B)
    (hAs : ∀ i, FactorShape22 ↥(A i)) (hBs : ∀ j, FactorShape22 ↥(B j)) :
    ∃ σ : Fin m ≃ Fin m', ∀ i, A i = B (σ i) := by
  have hZ := P22w.center_eq_bot_of_isInternalDirect hA fun i => P22w.center_eq_bot_of_factorShape22 (hAs i)
  obtain ⟨σ, hσ⟩ := P22w.exists_equiv_of_isIndexedDirectProduct (P22w.isIndexedDirectProduct_subgroupOf hA)
    (P22w.isIndexedDirectProduct_subgroupOf hB)
    (fun i => Sigma3Dec.isIndecomposableGroup_of_mulEquiv
      (subgroupOfEquivOfLe (P22w.le_of_isInternalDirect hA i)) (P22w.isIndecomposable_of_factorShape22 (hAs i)))
    (fun j => Sigma3Dec.isIndecomposableGroup_of_mulEquiv
      (subgroupOfEquivOfLe (P22w.le_of_isInternalDirect hB j)) (P22w.isIndecomposable_of_factorShape22 (hBs j)))
    hZ
  refine ⟨σ, fun i => ?_⟩
  have h := subgroupOf_inj.1 (hσ i)
  rwa [inf_of_le_left (P22w.le_of_isInternalDirect hA i), inf_of_le_left (P22w.le_of_isInternalDirect hB (σ i))]
    at h

theorem uc22p22wg_nbarSplit_unique {G : Type} [Group G] [Finite G] (D : Data G) {m m' : ℕ}
    {Nb : Fin m → Subgroup (MBar D.M D.U)} {Nb' : Fin m' → Subgroup (MBar D.M D.U)}
    (h : NbarSplit D Nb) (h' : NbarSplit D Nb') : ∃ σ : Fin m ≃ Fin m', ∀ i, Nb i = Nb' (σ i) :=
  uc22p22wg_remak h.1 h'.1 h.2 h'.2

end CFSG.LocalAnalysis.UniquenessCase.UC22
