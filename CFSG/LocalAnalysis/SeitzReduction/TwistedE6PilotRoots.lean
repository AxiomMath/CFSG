module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotAmalgam
public import CFSG.LocalAnalysis.SeitzReduction.EPilotRoots
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6ClassListBasic
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6ClassesReps
public import CFSG.LieType.Chevalley.GraphFixedF4GroupRestriction
public import CFSG.LieType.Chevalley.GraphFixedF4Intertwiner
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.Unitary
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneEInner
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

local instance twistedE6PilotRootsNeZeroE6 : NeZero TwistTag.E6.tag.rank := ⟨by decide⟩

local instance twistedE6PilotRootsNeZeroF4 : NeZero Tag.F4.rank := ⟨by decide⟩

local instance twistedE6PilotRootsNeZeroFolded : NeZero TwistTag.E6.foldedTag.rank := ⟨by decide⟩

local notation "ρ" => permLattice TwistTag.E6.perm

@[expose] def relSet (J : Finset (Fin TwistTag.E6.tag.rank)) : Finset (Fin Tag.F4.rank) :=
  J.image e6IndexToF4

theorem mem_orbit_f4FoldedIndex_iff (i : Fin TwistTag.E6.tag.rank) (a : Fin Tag.F4.rank) :
    i ∈ TwistTag.E6.orbit (f4FoldedIndex a) ↔ e6IndexToF4 i = a := by
  revert i a
  decide

theorem e6ToF4_apply_eq_sum (γ : Fin TwistTag.E6.tag.rank → ℤ) (a : Fin Tag.F4.rank) :
    e6ToF4 γ a = ∑ i ∈ TwistTag.E6.orbit (f4FoldedIndex a), γ i := by
  fin_cases a
  · change γ 1 = ∑ i ∈ ({1} : Finset (Fin TwistTag.E6.tag.rank)), γ i
    rw [Finset.sum_singleton]
  · change γ 3 = ∑ i ∈ ({3} : Finset (Fin TwistTag.E6.tag.rank)), γ i
    rw [Finset.sum_singleton]
  · change γ 2 + γ 4 = ∑ i ∈ ({2, 4} : Finset (Fin TwistTag.E6.tag.rank)), γ i
    rw [Finset.sum_pair (by decide)]
  · change γ 0 + γ 5 = ∑ i ∈ ({0, 5} : Finset (Fin TwistTag.E6.tag.rank)), γ i
    rw [Finset.sum_pair (by decide)]

theorem mem_relSet_iff {J : Finset (Fin TwistTag.E6.tag.rank)} {a : Fin Tag.F4.rank} :
    a ∈ relSet J ↔ ∃ i ∈ J, e6IndexToF4 i = a :=
  Finset.mem_image

theorem card_relSet_le (J : Finset (Fin TwistTag.E6.tag.rank)) : (relSet J).card ≤ J.card :=
  Finset.card_image_le

theorem e6ToF4_eq_zero_of_not_mem_relSet {J : Finset (Fin TwistTag.E6.tag.rank)}
    {δ : Fin TwistTag.E6.tag.rank → ℤ} (hδ : ∀ i ∉ J, δ i = 0) {a : Fin Tag.F4.rank}
    (ha : a ∉ relSet J) : e6ToF4 δ a = 0 := by
  rw [e6ToF4_apply_eq_sum]
  exact Finset.sum_eq_zero fun i hi => hδ i fun hiJ =>
    ha (mem_relSet_iff.2 ⟨i, hiJ, (mem_orbit_f4FoldedIndex_iff i a).1 hi⟩)

theorem e6ToF4_check : ∀ γ ∈ rootFinset TwistTag.E6.tag,
    (ρ γ = γ ↔ iform (e6ToF4 γ) (e6ToF4 γ) = 4) ∧ (ρ γ ≠ γ → iform γ (ρ γ) = 0) := by
  decide +kernel

theorem card_fixed_check :
    ((rootFinset TwistTag.E6.tag).filter fun γ => ρ γ = γ).card = 24 ∧
      ((rootFinset TwistTag.E6.tag).filter fun γ => ρ γ ≠ γ).card = 48 ∧
      ((rootFinset .F4).filter fun b => iform b b = 4).card = 24 ∧
      ((rootFinset .F4).filter fun b => iform b b = 2).card = 24 := by
  decide +kernel

section RelativeRoots

variable {γ : Fin TwistTag.E6.tag.rank → ℤ}

theorem permLattice_eq_self_iff (hγ : IsRoot TwistTag.E6.tag γ) :
    ρ γ = γ ↔ iform (e6ToF4 γ) (e6ToF4 γ) = 4 :=
  (e6ToF4_check γ (mem_rootFinset.2 hγ)).1

theorem iform_permLattice_eq_zero (hγ : IsRoot TwistTag.E6.tag γ) (h : ρ γ ≠ γ) :
    iform γ (ρ γ) = 0 :=
  (e6ToF4_check γ (mem_rootFinset.2 hγ)).2 h

end RelativeRoots

theorem e6ToF4_distinguished :
    e6ToF4 e6HighestRoot = F4Pilot.rootR ∧ e6ToF4 twistedE6ClassRootU = F4Pilot.rootS ∧
      e6ToF4 twistedE6ClassRootU' = F4Pilot.rootS ∧
      e6ToF4 twistedE6ClassRootB = F4Pilot.root1242 := by
  decide +kernel

theorem iform_e6HighestRoot
    (v : Fin TwistTag.E6.tag.rank → ℤ) :
    iform v e6HighestRoot = v 1 := by
  rw [iform_comm]
  exact EPilot.iform_highRoot (τ := .E6) (Or.inl rfl) v

theorem highRootPerp_check :
    (∀ δ ∈ rootFinset TwistTag.E6.tag, (iform δ e6HighestRoot = 0 ↔ δ 1 = 0)) ∧
      ((rootFinset TwistTag.E6.tag).filter fun δ => δ 1 = 0).card = 30 := by
  decide +kernel

theorem shortWeight_check :
    iform twistedE6ClassRootU twistedE6ClassRootU' = 0 ∧
      (∀ δ ∈ rootFinset TwistTag.E6.tag,
        -2 ≤ iform δ twistedE6ClassRootU + iform δ twistedE6ClassRootU' ∧
          iform δ twistedE6ClassRootU + iform δ twistedE6ClassRootU' ≤ 2) ∧
      ((rootFinset TwistTag.E6.tag).filter fun δ =>
        iform δ twistedE6ClassRootU + iform δ twistedE6ClassRootU' = 2).card = 8 ∧
      ((rootFinset TwistTag.E6.tag).filter fun δ =>
        iform δ twistedE6ClassRootU + iform δ twistedE6ClassRootU' = 1).card = 16 ∧
      ((rootFinset TwistTag.E6.tag).filter fun δ =>
        iform δ twistedE6ClassRootU + iform δ twistedE6ClassRootU' = 0).card = 24 ∧
      ((rootFinset TwistTag.E6.tag).filter fun δ =>
        iform δ twistedE6ClassRootU + iform δ twistedE6ClassRootU' = -1).card = 16 ∧
      ((rootFinset TwistTag.E6.tag).filter fun δ =>
        iform δ twistedE6ClassRootU + iform δ twistedE6ClassRootU' = -2).card = 8 := by
  decide +kernel

theorem shortKernel_check : ∀ δ ∈ rootFinset TwistTag.E6.tag,
    (iform δ twistedE6ClassRootU + iform δ twistedE6ClassRootU' = 0 ↔ δ 0 = 0 ∧ δ 5 = 0) := by
  decide +kernel

theorem shortKernel_iff {δ : Fin TwistTag.E6.tag.rank → ℤ}
    (hδ : IsRoot TwistTag.E6.tag δ) :
    iform δ twistedE6ClassRootU + iform δ (ρ twistedE6ClassRootU) = 0 ↔ δ 0 = 0 ∧ δ 5 = 0 := by
  rw [permLattice_twistedE6ClassRootU]
  exact shortKernel_check δ (mem_rootFinset.2 hδ)

theorem shortPerp_check :
    (∀ δ ∈ rootFinset TwistTag.E6.tag, iform δ twistedE6ClassRootU = 0 →
      iform δ twistedE6ClassRootU' = 0 → ρ δ = δ) ∧
      ((rootFinset TwistTag.E6.tag).filter fun δ =>
        iform δ twistedE6ClassRootU = 0 ∧ iform δ twistedE6ClassRootU' = 0).card = 12 := by
  decide +kernel

theorem d4Perp_check :
    (∀ δ ∈ rootFinset TwistTag.E6.tag, ¬ (iform δ (Pi.single 1 1) = 0 ∧
      iform δ (Pi.single 2 1) = 0 ∧ iform δ (Pi.single 3 1) = 0 ∧
        iform δ (Pi.single 4 1) = 0)) ∧
      ((rootFinset TwistTag.E6.tag).filter fun δ => δ 0 = 0 ∧ δ 5 = 0).card = 24 := by
  decide +kernel

theorem rootB_check :
    ρ twistedE6ClassRootB = twistedE6ClassRootB ∧
      (∀ i : Fin TwistTag.E6.tag.rank,
        iform (Pi.single i 1) twistedE6ClassRootB = 0 ↔ i = 0 ∨ i = 1 ∨ i = 5) ∧
      ((rootFinset TwistTag.E6.tag).filter fun δ =>
        iform δ twistedE6ClassRootB = 0).card = 30 := by
  decide +kernel

theorem placement_check {J : Finset (Fin TwistTag.E6.tag.rank)} (hJ : J.card ≤ 2)
    {δ : Fin TwistTag.E6.tag.rank → ℤ} (hδ : ∀ i ∉ J, δ i = 0) {a : Fin Tag.F4.rank}
    (ha : a ∉ (F4Pilot.amalgamPlacement (relSet J)).nodes) : e6ToF4 δ a = 0 :=
  e6ToF4_eq_zero_of_not_mem_relSet hδ fun h =>
    ha (F4Pilot.subset_nodes_amalgamPlacement ((card_relSet_le J).trans hJ) h)

theorem placement_table : ∀ J : Finset (Fin TwistTag.E6.tag.rank), J.card ≤ 2 →
    (F4Pilot.amalgamPlacement (relSet J) = .X' ↔ J = {0, 1} ∨ J = {1, 5}) ∧
      (F4Pilot.amalgamPlacement (relSet J) = .Y ↔ J = {1} ∨ J = {1, 2} ∨ J = {1, 3} ∨
        J = {1, 4}) := by
  decide +kernel

theorem nodes_inter_check :
    F4Pilot.AmalgamNeighbour.X.nodes ∩ F4Pilot.AmalgamNeighbour.Y.nodes = {1, 2} ∧
      F4Pilot.AmalgamNeighbour.X.nodes ∩ F4Pilot.AmalgamNeighbour.X'.nodes = {3} ∧
      F4Pilot.AmalgamNeighbour.Y.nodes ∩ F4Pilot.AmalgamNeighbour.X'.nodes = {0} ∧
      TwistTag.E6.orbit (f4FoldedIndex 1) ∪ TwistTag.E6.orbit (f4FoldedIndex 2) = {2, 3, 4} := by
  decide +kernel

@[expose] def rootE15 : Fin TwistTag.E6.tag.rank → ℤ := ![1, 0, 1, 1, 1, 0]

@[expose] def rootE26 : Fin TwistTag.E6.tag.rank → ℤ := ![0, 0, 1, 1, 1, 1]

@[expose] def relRoot0121 : Fin Tag.F4.rank → ℤ := ![0, 1, 2, 1]

theorem repRoots_check :
    (ρ (Pi.single 3 1) = Pi.single 3 1 ∧
        iform (Pi.single 3 1 : Fin TwistTag.E6.tag.rank → ℤ) e6HighestRoot = 0 ∧
        rootE15 ∈ rootFinset TwistTag.E6.tag ∧ ρ rootE15 = rootE26 ∧
        iform rootE15 rootE26 = 0 ∧ rootE15 1 = 0 ∧ rootE26 1 = 0 ∧
        e6ToF4 rootE15 = relRoot0121 ∧ iform F4Pilot.rootR (e6ToF4 rootE15) = 0) ∧
      (ρ (Pi.single 1 1) = Pi.single 1 1 ∧
        iform (Pi.single 1 1 : Fin TwistTag.E6.tag.rank → ℤ) twistedE6ClassRootU = 0 ∧
        iform (Pi.single 1 1 : Fin TwistTag.E6.tag.rank → ℤ) twistedE6ClassRootU' = 0 ∧
        ρ (Pi.single 2 1) = Pi.single 4 1 ∧
        iform (Pi.single 2 1 : Fin TwistTag.E6.tag.rank → ℤ) (Pi.single 4 1) = 0 ∧
        iform (Pi.single 2 1 : Fin TwistTag.E6.tag.rank → ℤ) twistedE6ClassRootU +
          iform (Pi.single 2 1 : Fin TwistTag.E6.tag.rank → ℤ) twistedE6ClassRootU' = 0 ∧
        e6ToF4 (Pi.single 2 1 : Fin TwistTag.E6.tag.rank → ℤ) = Pi.single 2 1 ∧
        iform F4Pilot.rootS (e6ToF4 (Pi.single 2 1 : Fin TwistTag.E6.tag.rank → ℤ)) = 0) := by
  decide +kernel

theorem isRoot_rootE15 :
    IsRoot TwistTag.E6.tag rootE15 ∧ IsRoot TwistTag.E6.tag rootE26 := by
  have h : rootE15 ∈ rootFinset TwistTag.E6.tag ∧ rootE26 ∈ rootFinset TwistTag.E6.tag := by
    decide +kernel
  exact ⟨mem_rootFinset.1 h.1, mem_rootFinset.1 h.2⟩

@[expose] def relWordTX : List (Fin TwistTag.E6.foldedTag.rank) := [3, 1, 2, 0, 1, 2, 3]

@[expose] def relWordTY : List (Fin TwistTag.E6.foldedTag.rank) := [2, 1, 2, 0, 1, 2, 3]

@[expose] def relWordUX : List (Fin TwistTag.E6.foldedTag.rank) := [3, 2, 0, 1, 0]

@[expose] def relWordUY : List (Fin TwistTag.E6.foldedTag.rank) := [2, 3, 0, 1, 2, 0, 1, 0]

@[expose] def relWordXPrime : List (Fin TwistTag.E6.foldedTag.rank) := [2, 3]

theorem relWords_check :
    twistedE6RelAct relWordTX e6HighestRoot = Pi.single 3 1 ∧
      twistedE6RelAct relWordTY e6HighestRoot = Pi.single 1 1 ∧
      twistedE6RelAct relWordUX twistedE6ClassRootU = rootE15 ∧
      twistedE6RelAct relWordUX twistedE6ClassRootU' = rootE26 ∧
      twistedE6RelAct relWordUY twistedE6ClassRootU = Pi.single 2 1 ∧
      twistedE6RelAct relWordUY twistedE6ClassRootU' = Pi.single 4 1 ∧
      twistedE6RelAct relWordXPrime e6HighestRoot = twistedE6ClassRootB := by
  decide +kernel

theorem conj_mul_distrib {M : Type*} [Group M] (n a b : M) :
    n * (a * b) * n⁻¹ = (n * a * n⁻¹) * (n * b * n⁻¹) := by
  group

section Transport

variable {K : Type} [Field K] [CharP K 2]

theorem conj_relWordTX_pinnedX_highRoot (c : K) :
    twistedE6RelWeyl K relWordTX * pinnedX TwistTag.E6.tag K e6HighestRoot c *
        (twistedE6RelWeyl K relWordTX)⁻¹ = pinnedX TwistTag.E6.tag K (Pi.single 3 1) c := by
  rw [twistedE6RelWeyl_conj_pinnedX relWordTX isRoot_e6HighestRoot c, relWords_check.1]

theorem conj_relWordTY_pinnedX_highRoot (c : K) :
    twistedE6RelWeyl K relWordTY * pinnedX TwistTag.E6.tag K e6HighestRoot c *
        (twistedE6RelWeyl K relWordTY)⁻¹ = pinnedX TwistTag.E6.tag K (Pi.single 1 1) c := by
  rw [twistedE6RelWeyl_conj_pinnedX relWordTY isRoot_e6HighestRoot c, relWords_check.2.1]

theorem conj_relWordUX_twistedE6ClassU :
    twistedE6RelWeyl K relWordUX * twistedE6ClassU K * (twistedE6RelWeyl K relWordUX)⁻¹ =
      pinnedX TwistTag.E6.tag K rootE15 1 * pinnedX TwistTag.E6.tag K rootE26 1 := by
  rw [twistedE6ClassU, conj_mul_distrib,
    twistedE6RelWeyl_conj_pinnedX relWordUX isRoot_twistedE6ClassRoots.1,
    twistedE6RelWeyl_conj_pinnedX relWordUX isRoot_twistedE6ClassRoots.2.1,
    relWords_check.2.2.1, relWords_check.2.2.2.1]

theorem conj_relWordUY_twistedE6ClassU :
    twistedE6RelWeyl K relWordUY * twistedE6ClassU K * (twistedE6RelWeyl K relWordUY)⁻¹ =
      pinnedX TwistTag.E6.tag K (Pi.single 2 1) 1 *
        pinnedX TwistTag.E6.tag K (Pi.single 4 1) 1 := by
  rw [twistedE6ClassU, conj_mul_distrib,
    twistedE6RelWeyl_conj_pinnedX relWordUY isRoot_twistedE6ClassRoots.1,
    twistedE6RelWeyl_conj_pinnedX relWordUY isRoot_twistedE6ClassRoots.2.1,
    relWords_check.2.2.2.2.1, relWords_check.2.2.2.2.2.1]

theorem conj_relWordXPrime_pinnedX_highRoot (c : K) :
    twistedE6RelWeyl K relWordXPrime * pinnedX TwistTag.E6.tag K e6HighestRoot c *
        (twistedE6RelWeyl K relWordXPrime)⁻¹ =
      pinnedX TwistTag.E6.tag K twistedE6ClassRootB c := by
  rw [twistedE6RelWeyl_conj_pinnedX relWordXPrime isRoot_e6HighestRoot c,
    relWords_check.2.2.2.2.2.2]

end Transport

end CFSG.SeitzReduction.TwistedE6Pilot
