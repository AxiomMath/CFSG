module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphFirstRow
import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The second rooted incidence count for the Suzuki odd graph

The four root neighbours have three neighbours each in the 12-point
fibre-four layer.  Transitivity on that layer and double-counting therefore
show that every fibre-four vertex has exactly one root neighbour.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

private def commutingGraph_smulHom
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (g : G) : commutingGraph c →g commutingGraph c where
  toFun V := g • V
  map_rel' := by
    intro V W hVW
    exact (commutingGraph.adj_smul_iff c g V W).mpr hVW

private def firstCase_rootComponentSubgroup
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) : Subgroup G where
  carrier := {g | (commutingGraph c).Reachable
    (UConjugates.base c) (g • UConjugates.base c)}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    have hh' := hh.map (commutingGraph_smulHom c g)
    change (commutingGraph c).Reachable (g • UConjugates.base c)
      (g • (h • UConjugates.base c)) at hh'
    exact hg.trans (by simpa only [mul_smul] using hh')
  inv_mem' := by
    intro g hg
    change (commutingGraph c).Reachable (UConjugates.base c)
      (g⁻¹ • UConjugates.base c)
    have hg' := hg.map (commutingGraph_smulHom c g⁻¹)
    change (commutingGraph c).Reachable (g⁻¹ • UConjugates.base c)
      (g⁻¹ • (g • UConjugates.base c)) at hg'
    exact (by simpa only [← mul_smul, inv_mul_cancel, one_smul] using hg'.symm)

/-- The commuting graph is connected.  The subgroup of elements moving the
root inside its connected component contains the root stabilizer `Ĥ` and one
element outside `Ĥ`, so maximality of `Ĥ` makes that subgroup all of `G`. -/
public theorem firstCase_commutingGraph_connected
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c) :
    (commutingGraph c).Connected := by
  classical
  let C := firstCase_rootComponentSubgroup c
  have hHle : c.Hhat ≤ C := by
    intro h hh
    have hfix : (h : G) • UConjugates.base c = UConjugates.base c := by
      apply MulAction.mem_stabilizer_iff.mp
      rw [commutingGraph.stabilizer_base_eq_hhat hmin c hfirst]
      exact hh
    change (commutingGraph c).Reachable (UConjugates.base c)
      ((h : G) • UConjugates.base c)
    rw [hfix]
  have hCne : C ≠ c.Hhat := by
    have hA : Nat.card (lineNeighborSet c) = 4 :=
      neighbor_card_eq_four hmin c hfirst d
    obtain ⟨V⟩ := (Nat.card_pos_iff.mp
      (by omega : 0 < Nat.card (lineNeighborSet c))).1
    rcases V.1.2 with ⟨g, hg⟩
    have hgb : g • UConjugates.base c = V.1 := by
      apply Subtype.ext
      rw [UConjugates.smul_def]
      change conjugateSubgroup c.U g = V.1.1
      exact hg.symm
    have hgC : g ∈ C := by
      change (commutingGraph c).Reachable (UConjugates.base c)
        (g • UConjugates.base c)
      rw [hgb]
      exact ((commutingGraph_adj_iff c _ _).mpr
        ⟨V.2.1.symm, V.2.2⟩).reachable
    have hgH : g ∉ c.Hhat := by
      intro hgH
      have hfix : g • UConjugates.base c = UConjugates.base c := by
        apply MulAction.mem_stabilizer_iff.mp
        rw [commutingGraph.stabilizer_base_eq_hhat hmin c hfirst]
        exact hgH
      exact V.2.1 (hgb.symm.trans hfix)
    intro hCH
    exact hgH (hCH ▸ hgC)
  have hCtop : C = ⊤ := by
    rcases (c.Hhat_maximal.le_iff).mp hHle with htop | heq
    · exact htop
    · exact False.elim (hCne heq)
  let : Nonempty (UConjugates c) := ⟨UConjugates.base c⟩
  apply SimpleGraph.Connected.mk
  intro V W
  have root_reachable (X : UConjugates c) :
      (commutingGraph c).Reachable (UConjugates.base c) X := by
    rcases X.2 with ⟨g, hg⟩
    have hgC : g ∈ C := by rw [hCtop]; trivial
    change (commutingGraph c).Reachable (UConjugates.base c) X
    have hgb : g • UConjugates.base c = X := by
      apply Subtype.ext
      rw [UConjugates.smul_def]
      change conjugateSubgroup c.U g = X.1
      exact hg.symm
    rw [← hgb]
    exact hgC
  exact (root_reachable V).symm.trans (root_reachable W)

private theorem firstCaseRootLayer_smul_mem
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (n : ℕ) (h : c.Hhat) {V : UConjugates c}
    (hV : (cosetLineEquiv hmin c hfirst).symm V ≠
        cosetInvolution_base c.Hhat ∧
      Nat.card (cosetInvolution_fiber c.Hhat
        ((cosetLineEquiv hmin c hfirst).symm V)) = n) :
    (cosetLineEquiv hmin c hfirst).symm ((h : G) • V) ≠
        cosetInvolution_base c.Hhat ∧
      Nat.card (cosetInvolution_fiber c.Hhat
        ((cosetLineEquiv hmin c hfirst).symm ((h : G) • V))) = n := by
  let e := cosetLineEquiv hmin c hfirst
  have heq : e.symm ((h : G) • V) = (h : G) • e.symm V := by
    apply e.injective
    rw [e.apply_symm_apply, cosetLineEquiv_smul, e.apply_symm_apply]
  rw [heq]
  exact ⟨smul_base_ne c.Hhat h.2 hV.1,
    (fiber_card_smul c.Hhat h.2 (e.symm V)).trans hV.2⟩

private theorem firstCaseRootLayerTwo_smul_mem
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (h : c.Hhat) {V : UConjugates c}
    (hV : V ∈ firstCaseRootLayerTwo hmin c hfirst) :
    (h : G) • V ∈ firstCaseRootLayerTwo hmin c hfirst :=
  firstCaseRootLayer_smul_mem hmin c hfirst 2 h hV

private theorem firstCaseRootLayerFour_smul_mem
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (h : c.Hhat) {V : UConjugates c}
    (hV : V ∈ firstCaseRootLayerFour hmin c hfirst) :
    (h : G) • V ∈ firstCaseRootLayerFour hmin c hfirst :=
  firstCaseRootLayer_smul_mem hmin c hfirst 4 h hV

private def fourTwo_incidence_equiv_left
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    {V W : UConjugates c}
    (h : c.Hhat) (hVW : (h : G) • V = W) :
    {X : {X : UConjugates c // X ∈ firstCaseRootLayerTwo hmin c hfirst} //
        (commutingGraph c).Adj V X.1} ≃
      {X : {X : UConjugates c // X ∈ firstCaseRootLayerTwo hmin c hfirst} //
        (commutingGraph c).Adj W X.1} := by
  let f : {X : {X : UConjugates c // X ∈ firstCaseRootLayerTwo hmin c hfirst} //
        (commutingGraph c).Adj V X.1} →
      {X : {X : UConjugates c // X ∈ firstCaseRootLayerTwo hmin c hfirst} //
        (commutingGraph c).Adj W X.1} := fun X => by
    let X' : {X : UConjugates c // X ∈ firstCaseRootLayerTwo hmin c hfirst} :=
      ⟨(h : G) • X.1.1,
        firstCaseRootLayerTwo_smul_mem hmin c hfirst h X.1.2⟩
    have hAdj := (commutingGraph.adj_smul_iff c (h : G) V X.1.1).mpr X.2
    have hAdj' : (commutingGraph c).Adj W X'.1 := by
      simpa only [X', hVW] using hAdj
    exact ⟨X', hAdj'⟩
  have hf : Function.Bijective f := by
    constructor
    · intro X Y hXY
      apply Subtype.ext
      apply Subtype.ext
      apply (MulAction.injective (h : G))
      exact congrArg (fun Z => Z.1.1) hXY
    · intro Y
      let X' : {X : UConjugates c // X ∈ firstCaseRootLayerTwo hmin c hfirst} :=
        ⟨(h⁻¹ : G) • Y.1.1,
          firstCaseRootLayerTwo_smul_mem hmin c hfirst (h⁻¹) Y.1.2⟩
      have hWinv : (h⁻¹ : G) • W = V := by
        calc
          (h⁻¹ : G) • W = (h⁻¹ : G) • ((h : G) • V) := by rw [hVW]
          _ = V := by rw [← mul_smul]; simp
      have hAdj := (commutingGraph.adj_smul_iff c (h⁻¹ : G) W Y.1.1).mpr Y.2
      have hAdj' : (commutingGraph c).Adj V X'.1 := by
        simpa only [X', hWinv] using hAdj
      refine ⟨⟨X', hAdj'⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      dsimp [f, X']
      rw [← mul_smul]
      simp
  exact Equiv.ofBijective f hf

private def fourTwo_incidence_equiv_right
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    {V W : UConjugates c}
    (h : c.Hhat) (hVW : (h : G) • V = W) :
    {X : {X : UConjugates c // X ∈ firstCaseRootLayerFour hmin c hfirst} //
        (commutingGraph c).Adj X.1 V} ≃
      {X : {X : UConjugates c // X ∈ firstCaseRootLayerFour hmin c hfirst} //
        (commutingGraph c).Adj X.1 W} := by
  let f : {X : {X : UConjugates c // X ∈ firstCaseRootLayerFour hmin c hfirst} //
        (commutingGraph c).Adj X.1 V} →
      {X : {X : UConjugates c // X ∈ firstCaseRootLayerFour hmin c hfirst} //
        (commutingGraph c).Adj X.1 W} := fun X => by
    let X' : {X : UConjugates c // X ∈ firstCaseRootLayerFour hmin c hfirst} :=
      ⟨(h : G) • X.1.1,
        firstCaseRootLayerFour_smul_mem hmin c hfirst h X.1.2⟩
    have hAdj := (commutingGraph.adj_smul_iff c (h : G) X.1.1 V).mpr X.2
    have hAdj' : (commutingGraph c).Adj X'.1 W := by
      simpa only [X', hVW] using hAdj
    exact ⟨X', hAdj'⟩
  have hf : Function.Bijective f := by
    constructor
    · intro X Y hXY
      apply Subtype.ext
      apply Subtype.ext
      apply (MulAction.injective (h : G))
      exact congrArg (fun Z => Z.1.1) hXY
    · intro Y
      let X' : {X : UConjugates c // X ∈ firstCaseRootLayerFour hmin c hfirst} :=
        ⟨(h⁻¹ : G) • Y.1.1,
          firstCaseRootLayerFour_smul_mem hmin c hfirst (h⁻¹) Y.1.2⟩
      have hWinv : (h⁻¹ : G) • W = V := by
        calc
          (h⁻¹ : G) • W = (h⁻¹ : G) • ((h : G) • V) := by rw [hVW]
          _ = V := by rw [← mul_smul]; simp
      have hAdj := (commutingGraph.adj_smul_iff c (h⁻¹ : G) Y.1.1 W).mpr Y.2
      have hAdj' : (commutingGraph c).Adj X'.1 V := by
        simpa only [X', hWinv] using hAdj
      refine ⟨⟨X', hAdj'⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      dsimp [f, X']
      rw [← mul_smul]
      simp
  exact Equiv.ofBijective f hf

private def rootFour_incidence_equiv
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    {V W : UConjugates c}
    (hV : V ∈ firstCaseRootLayerFour hmin c hfirst)
    (hW : W ∈ firstCaseRootLayerFour hmin c hfirst)
    (h : c.Hhat) (hVW : (h : G) • V = W) :
    {X : lineNeighborSet c // (commutingGraph c).Adj X.1 V} ≃
      {X : lineNeighborSet c // (commutingGraph c).Adj X.1 W} := by
  let f : {X : lineNeighborSet c // (commutingGraph c).Adj X.1 V} →
      {X : lineNeighborSet c // (commutingGraph c).Adj X.1 W} := fun X => by
    let X' := firstCase_rootNeighbor_smul hmin c hfirst h X.1
    have hAdj := (commutingGraph.adj_smul_iff c (h : G) X.1 V).mpr X.2
    have hAdjW : (commutingGraph c).Adj X'.1 W := by
      simpa only [X', firstCase_rootNeighbor_smul_val, hVW] using hAdj
    exact ⟨X', hAdjW⟩
  have hf : Function.Bijective f := by
    constructor
    · intro X Y hXY
      apply Subtype.ext
      have hXY' : firstCase_rootNeighbor_smul hmin c hfirst h X.1 =
          firstCase_rootNeighbor_smul hmin c hfirst h Y.1 := congrArg Subtype.val hXY
      calc
        X.1 = firstCase_rootNeighbor_smul hmin c hfirst (h⁻¹)
            (firstCase_rootNeighbor_smul hmin c hfirst h X.1) :=
          (firstCase_rootNeighbor_smul_inv hmin c hfirst h X.1).symm
        _ = firstCase_rootNeighbor_smul hmin c hfirst (h⁻¹)
            (firstCase_rootNeighbor_smul hmin c hfirst h Y.1) := by rw [hXY']
        _ = Y.1 := firstCase_rootNeighbor_smul_inv hmin c hfirst h Y.1
    · intro X
      let X' := firstCase_rootNeighbor_smul hmin c hfirst (h⁻¹) X.1
      have hWinv : (h⁻¹ : G) • W = V := by
        calc
          (h⁻¹ : G) • W = (h⁻¹ : G) • ((h : G) • V) := by rw [hVW]
          _ = V := by rw [← mul_smul]; simp
      have hAdj := (commutingGraph.adj_smul_iff c (h⁻¹ : G) X.1 W).mpr X.2
      have hAdjV : (commutingGraph c).Adj X'.1 V := by
        have hxval : (X' : UConjugates c) = (h⁻¹ : G) • X.1 :=
          firstCase_rootNeighbor_smul_val hmin c hfirst (h⁻¹) X.1
        rw [hxval]
        simpa only [hWinv] using hAdj
      refine ⟨⟨X', hAdjV⟩, ?_⟩
      apply Subtype.ext
      dsimp [f, X']
      simpa using firstCase_rootNeighbor_smul_inv hmin c hfirst (h⁻¹) X.1
  exact Equiv.ofBijective f hf

/-- Every fibre-four vertex has exactly one root neighbour. -/
public theorem firstCase_rootLayerFour_rootNeighbor_card_one
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c)
    (W : UConjugates c)
    (hW : W ∈ firstCaseRootLayerFour hmin c hfirst) :
    Nat.card {V : lineNeighborSet c // (commutingGraph c).Adj V.1 W} = 1 := by
  classical
  let A := lineNeighborSet c
  let B := {W : UConjugates c // W ∈ firstCaseRootLayerFour hmin c hfirst}
  let I : Type u := {p : A × B // (commutingGraph c).Adj p.1.1 p.2.1}
  let eA : I ≃ Σ V : A, {W : B // (commutingGraph c).Adj V.1 W.1} :=
    { toFun := fun p => ⟨p.1.1, ⟨p.1.2, p.2⟩⟩
      invFun := fun p => ⟨⟨p.1, p.2.1⟩, p.2.2⟩
      left_inv := by intro p; rfl
      right_inv := by intro p; rfl }
  let eB : I ≃ Σ W : B, {V : A // (commutingGraph c).Adj V.1 W.1} :=
    { toFun := fun p => ⟨p.1.2, ⟨p.1.1, p.2⟩⟩
      invFun := fun p => ⟨⟨p.2.1, p.1⟩, p.2.2⟩
      left_inv := by intro p; rfl
      right_inv := by intro p; rfl }
  let : Fintype A := Fintype.ofFinite A
  let : Fintype B := Fintype.ofFinite B
  have hIcardA : Nat.card I =
      ∑ V : A, Nat.card {W : B // (commutingGraph c).Adj V.1 W.1} := by
    rw [Nat.card_congr eA, Nat.card_sigma]
  have hIcardB : Nat.card I =
      ∑ W : B, Nat.card {V : A // (commutingGraph c).Adj V.1 W.1} := by
    rw [Nat.card_congr eB, Nat.card_sigma]
  have hIeq : Nat.card I = 12 := by
    rw [hIcardA]
    calc
      (∑ V : A, Nat.card {W : B // (commutingGraph c).Adj V.1 W.1}) =
          ∑ _V : A, 3 := by
            apply Finset.sum_congr rfl
            intro V _
            have hcard := firstCase_rootNeighbor_four_neighbors_card_three
              hmin c hfirst d V
            exact hcard
      _ = 12 := by
        rw [Finset.sum_const, Finset.card_univ]
        have hA : Nat.card A = 4 := neighbor_card_eq_four hmin c hfirst d
        have hA' : Fintype.card A = 4 := by
          simpa [Nat.card_eq_fintype_card] using hA
        simp [hA']
  have hBcard : Nat.card B = 12 := firstCaseRootLayerFour_card hmin c hfirst d
  have hBcard' : Fintype.card B = 12 := by
    simpa [Nat.card_eq_fintype_card] using hBcard
  obtain ⟨W0⟩ := (Nat.card_pos_iff.mp (by omega : 0 < Nat.card B)).1
  let k : ℕ := Nat.card {V : A // (commutingGraph c).Adj V.1 W0.1}
  have hconst (W' : B) : Nat.card {V : A // (commutingGraph c).Adj V.1 W'.1} = k := by
    obtain ⟨h, hVW⟩ := firstCaseRootLayerFour_transitive hmin c hfirst d
      (V := W0.1) (W := W'.1) W0.2 W'.2
    let e := rootFour_incidence_equiv hmin c hfirst
      (V := W0.1) (W := W'.1) W0.2 W'.2 h hVW
    exact (Nat.card_congr e).symm
  have hIeq' : Nat.card I = 12 * k := by
    rw [hIcardB]
    simp_rw [hconst]
    simp [k, hBcard']
  have hk : k = 1 := by
    rw [hIeq'] at hIeq
    omega
  let W' : B := ⟨W, hW⟩
  have hcard := hconst W'
  rw [hk] at hcard
  simpa [A, W'] using hcard

private theorem firstCase_rootLayerTwo_not_lineNeighbor
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c) (V : UConjugates c)
    (hT : V ∈ firstCaseRootLayerTwo hmin c hfirst)
    (hN : V ∈ lineNeighbors c) : False := by
  have hzero := (firstCase_mem_lineNeighbors_iff_cosetLayer_zero
    hmin c hfirst d V).mp hN
  have hbad : (2 : ℕ) = 0 := hT.2.symm.trans hzero.2
  omega

private theorem firstCase_rootLayerFour_not_lineNeighbor
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c) (V : UConjugates c)
    (hF : V ∈ firstCaseRootLayerFour hmin c hfirst)
    (hN : V ∈ lineNeighbors c) : False := by
  have hzero := (firstCase_mem_lineNeighbors_iff_cosetLayer_zero
    hmin c hfirst d V).mp hN
  have hbad : (4 : ℕ) = 0 := hF.2.symm.trans hzero.2
  omega

private theorem firstCase_rootLayerTwo_not_rootLayerFour
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (V : UConjugates c)
    (hT : V ∈ firstCaseRootLayerTwo hmin c hfirst)
    (hF : V ∈ firstCaseRootLayerFour hmin c hfirst) : False := by
  have hbad : (2 : ℕ) = 4 := hT.2.symm.trans hF.2
  omega

private theorem firstCase_rootLayerTwo_not_adjacent_base
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c) (V : UConjugates c)
    (hT : V ∈ firstCaseRootLayerTwo hmin c hfirst) :
    ¬ (commutingGraph c).Adj V (UConjugates.base c) := by
  intro hAdj
  have hAdj' := (commutingGraph_adj_iff c _ _).mp hAdj.symm
  exact firstCase_rootLayerTwo_not_lineNeighbor hmin c hfirst d V hT
    ⟨hAdj'.1.symm, hAdj'.2⟩

/-- The cross-incidence degrees between the fibre-four and fibre-two layers
are respectively three and two.  Double-counting first leaves a zero-degree
alternative; connectedness of the commuting graph eliminates it. -/
public theorem firstCase_rootLayerFour_two_incidence
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c) :
    (∀ V : UConjugates c,
      V ∈ firstCaseRootLayerFour hmin c hfirst →
      Nat.card {W : {W : UConjugates c //
        W ∈ firstCaseRootLayerTwo hmin c hfirst} //
          (commutingGraph c).Adj V W.1} = 3) ∧
    (∀ W : UConjugates c,
      W ∈ firstCaseRootLayerTwo hmin c hfirst →
      Nat.card {V : {V : UConjugates c //
        V ∈ firstCaseRootLayerFour hmin c hfirst} //
          (commutingGraph c).Adj V.1 W} = 2) := by
  classical
  let F := {V : UConjugates c // V ∈ firstCaseRootLayerFour hmin c hfirst}
  let T := {W : UConjugates c // W ∈ firstCaseRootLayerTwo hmin c hfirst}
  let I : Type u := {p : F × T // (commutingGraph c).Adj p.1.1 p.2.1}
  let eF : I ≃ Σ V : F, {W : T // (commutingGraph c).Adj V.1 W.1} :=
    { toFun := fun p => ⟨p.1.1, ⟨p.1.2, p.2⟩⟩
      invFun := fun p => ⟨⟨p.1, p.2.1⟩, p.2.2⟩
      left_inv := by intro p; rfl
      right_inv := by intro p; rfl }
  let eT : I ≃ Σ W : T, {V : F // (commutingGraph c).Adj V.1 W.1} :=
    { toFun := fun p => ⟨p.1.2, ⟨p.1.1, p.2⟩⟩
      invFun := fun p => ⟨⟨p.2.1, p.1⟩, p.2.2⟩
      left_inv := by intro p; rfl
      right_inv := by intro p; rfl }
  let : Fintype F := Fintype.ofFinite F
  let : Fintype T := Fintype.ofFinite T
  have hFcard : Nat.card F = 12 := firstCaseRootLayerFour_card hmin c hfirst d
  have hTcard : Nat.card T = 18 := firstCaseRootLayerTwo_card hmin c hfirst d
  have hFcard' : Fintype.card F = 12 := by
    simpa [Nat.card_eq_fintype_card] using hFcard
  have hTcard' : Fintype.card T = 18 := by
    simpa [Nat.card_eq_fintype_card] using hTcard
  obtain ⟨F0⟩ := (Nat.card_pos_iff.mp (by omega : 0 < Nat.card F)).1
  obtain ⟨T0⟩ := (Nat.card_pos_iff.mp (by omega : 0 < Nat.card T)).1
  let b : ℕ := Nat.card {W : T // (commutingGraph c).Adj F0.1 W.1}
  let k : ℕ := Nat.card {V : F // (commutingGraph c).Adj V.1 T0.1}
  have hconstF (V : F) :
      Nat.card {W : T // (commutingGraph c).Adj V.1 W.1} = b := by
    obtain ⟨h, hFV⟩ := firstCaseRootLayerFour_transitive hmin c hfirst d
      (V := F0.1) (W := V.1) F0.2 V.2
    let e := fourTwo_incidence_equiv_left hmin c hfirst h hFV
    exact (Nat.card_congr e).symm
  have hconstT (W : T) :
      Nat.card {V : F // (commutingGraph c).Adj V.1 W.1} = k := by
    obtain ⟨h, hTW⟩ := firstCaseRootLayerTwo_transitive hmin c hfirst d
      (V := T0.1) (W := W.1) T0.2 W.2
    let e := fourTwo_incidence_equiv_right hmin c hfirst h hTW
    exact (Nat.card_congr e).symm
  have hIcardF : Nat.card I = 12 * b := by
    rw [Nat.card_congr eF, Nat.card_sigma]
    simp_rw [hconstF]
    simp [b, hFcard']
  have hIcardT : Nat.card I = 18 * k := by
    rw [Nat.card_congr eT, Nat.card_sigma]
    simp_rw [hconstT]
    simp [k, hTcard']
  have hbk : 12 * b = 18 * k := hIcardF.symm.trans hIcardT
  have hble : b ≤ 3 := by
    let B0 := {W : T // (commutingGraph c).Adj F0.1 W.1}
    let N0 := {V : lineNeighborSet c // (commutingGraph c).Adj V.1 F0.1}
    let Full := {W : UConjugates c // (commutingGraph c).Adj F0.1 W}
    let f : Sum B0 N0 → Full
      | Sum.inl W => ⟨W.1.1, W.2⟩
      | Sum.inr V => ⟨V.1.1, V.2.symm⟩
    have hf : Function.Injective f := by
      intro X Y hXY
      rcases X with X | X <;> rcases Y with Y | Y
      · congr 1
        apply Subtype.ext
        apply Subtype.ext
        have hval := congrArg Subtype.val hXY
        simpa [f] using hval
      · exfalso
        have hEq : X.1.1 = Y.1.1 := congrArg Subtype.val hXY
        have htwo : Y.1.1 ∈ firstCaseRootLayerTwo hmin c hfirst := hEq ▸ X.1.2
        exact firstCase_rootLayerTwo_not_lineNeighbor
          hmin c hfirst d Y.1.1 htwo Y.1.2
      · exfalso
        have hEq : X.1.1 = Y.1.1 := congrArg Subtype.val hXY
        have htwo : X.1.1 ∈ firstCaseRootLayerTwo hmin c hfirst := hEq ▸ Y.1.2
        exact firstCase_rootLayerTwo_not_lineNeighbor
          hmin c hfirst d X.1.1 htwo X.1.2
      · congr 1
        apply Subtype.ext
        apply Subtype.ext
        have hval := congrArg Subtype.val hXY
        simpa [f] using hval
    have hle := Nat.card_le_card_of_injective f hf
    have hB0 : Nat.card B0 = b := rfl
    have hN0 : Nat.card N0 = 1 :=
      firstCase_rootLayerFour_rootNeighbor_card_one hmin c hfirst d F0.1 F0.2
    have hFull : Nat.card Full = 4 :=
      firstCase_commutingGraph_degree_four hmin c hfirst d F0.1
    rw [Nat.card_sum, hB0, hN0, hFull] at hle
    omega
  by_cases hb0 : b = 0
  · exfalso
    have hzero (V : F) :
        Nat.card {W : T // (commutingGraph c).Adj V.1 W.1} = 0 := by
      rw [hconstF V, hb0]
    let S : Set (UConjugates c) :=
      {V | V = UConjugates.base c ∨ V ∈ lineNeighbors c ∨
        V ∈ firstCaseRootLayerFour hmin c hfirst}
    have hclosed : ∀ V : UConjugates c, V ∈ S → ∀ W : UConjugates c,
        (commutingGraph c).Adj V W → W ∈ S := by
      intro V hVS W hAdj
      rcases hVS with hbase | hN | hF
      · subst V
        have hAdj' := (commutingGraph_adj_iff c _ _).mp hAdj
        exact Or.inr (Or.inl ⟨hAdj'.1.symm, hAdj'.2⟩)
      · let VN : lineNeighborSet c := ⟨V, hN⟩
        rcases firstCase_rootNeighbor_adjacent_mem_base_or_four
          hmin c hfirst d VN W hAdj with hWbase | hWfour
        · exact Or.inl hWbase
        · exact Or.inr (Or.inr hWfour)
      · rcases firstCase_root_partition hmin c hfirst d W with
          hWbase | hWN | hWT | hWF
        · exact Or.inl hWbase
        · exact Or.inr (Or.inl hWN)
        · exfalso
          let z : {W : T // (commutingGraph c).Adj V W.1} :=
            ⟨⟨W, hWT⟩, hAdj⟩
          have hpos : 0 < Nat.card {W : T // (commutingGraph c).Adj V W.1} :=
            Nat.card_pos_iff.mpr ⟨Nonempty.intro z, inferInstance⟩
          have hz := hzero ⟨V, hF⟩
          rw [hz] at hpos
          omega
        · exact Or.inr (Or.inr hWF)
    let H : (commutingGraph c).Subgraph := (⊤ : (commutingGraph c).Subgraph).induce S
    have hclosure : ∀ V, V ∈ H.verts → ∀ W,
        (commutingGraph c).Adj V W → H.Adj V W := by
      intro V hV W hAdj
      have hVS : V ∈ S := by simpa [H] using hV
      have hWS : W ∈ S := hclosed V hVS W hAdj
      exact ⟨hVS, hWS, by simpa using hAdj⟩
    have hbaseS : UConjugates.base c ∈ H.verts := by
      change UConjugates.base c ∈ S
      exact Or.inl rfl
    have hTnotS : T0.1 ∉ S := by
      intro hmem
      rcases hmem with hbase | hN | hF
      · have hbase' : (cosetLineEquiv hmin c hfirst).symm
            (UConjugates.base c) = cosetInvolution_base c.Hhat := by
          apply (cosetLineEquiv hmin c hfirst).injective
          rw [(cosetLineEquiv hmin c hfirst).apply_symm_apply,
            cosetLineEquiv_base hmin c hfirst]
        exact T0.2.1 (by rw [hbase, hbase'])
      · have hzero' := (firstCase_mem_lineNeighbors_iff_cosetLayer_zero
          hmin c hfirst d T0.1).mp hN
        have hbad : (2 : ℕ) = 0 := T0.2.2.symm.trans hzero'.2
        omega
      · have hbad : (2 : ℕ) = 4 := T0.2.2.symm.trans hF.2
        omega
    have hr : (commutingGraph c).Reachable (UConjugates.base c) T0.1 :=
      (firstCase_commutingGraph_connected hmin c hfirst d).preconnected _ _
    have hTmemH : T0.1 ∈ H.verts := hr.mem_subgraphVerts hclosure hbaseS
    exact hTnotS (by simpa [H] using hTmemH)
  · have hb3 : b = 3 := by omega
    have hk2 : k = 2 := by omega
    constructor
    · intro V hV
      let V' : F := ⟨V, hV⟩
      have hcard := hconstF V'
      rw [hb3] at hcard
      simpa [F, T, V'] using hcard
    · intro W hW
      let W' : T := ⟨W, hW⟩
      have hcard := hconstT W'
      rw [hk2] at hcard
      simpa [F, T, W'] using hcard

/-- The fibre-four layer is a coclique.  Its one root-neighbour and three
fibre-two neighbours already exhaust degree four. -/
public theorem firstCase_rootLayerFour_internal_neighbors_card_zero
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c) (V : UConjugates c)
    (hV : V ∈ firstCaseRootLayerFour hmin c hfirst) :
    Nat.card {W : {W : UConjugates c //
      W ∈ firstCaseRootLayerFour hmin c hfirst} //
        (commutingGraph c).Adj V W.1} = 0 := by
  classical
  let T := {W : UConjugates c // W ∈ firstCaseRootLayerTwo hmin c hfirst}
  let F := {W : UConjugates c // W ∈ firstCaseRootLayerFour hmin c hfirst}
  let N0 := {W : lineNeighborSet c // (commutingGraph c).Adj W.1 V}
  let T0 := {W : T // (commutingGraph c).Adj V W.1}
  let F0 := {W : F // (commutingGraph c).Adj V W.1}
  let Full := {W : UConjugates c // (commutingGraph c).Adj V W}
  let f : Sum N0 (Sum T0 F0) → Full
    | Sum.inl W => ⟨W.1.1, W.2.symm⟩
    | Sum.inr (Sum.inl W) => ⟨W.1.1, W.2⟩
    | Sum.inr (Sum.inr W) => ⟨W.1.1, W.2⟩
  have hf : Function.Injective f := by
    intro X Y hXY
    rcases X with X | X
    · rcases Y with Y | Y
      · congr 1
        apply Subtype.ext
        apply Subtype.ext
        have hval := congrArg Subtype.val hXY
        simpa [f] using hval
      · rcases Y with Y | Y
        · exfalso
          have hval := congrArg Subtype.val hXY
          have hEq : X.1.1 = Y.1.1 := by simpa [f] using hval
          have hN : Y.1.1 ∈ lineNeighbors c := hEq ▸ X.1.2
          exact firstCase_rootLayerTwo_not_lineNeighbor
            hmin c hfirst d Y.1.1 Y.1.2 hN
        · exfalso
          have hval := congrArg Subtype.val hXY
          have hEq : X.1.1 = Y.1.1 := by simpa [f] using hval
          have hN : Y.1.1 ∈ lineNeighbors c := hEq ▸ X.1.2
          exact firstCase_rootLayerFour_not_lineNeighbor
            hmin c hfirst d Y.1.1 Y.1.2 hN
    · rcases X with X | X
      · rcases Y with Y | Y
        · exfalso
          have hval := congrArg Subtype.val hXY
          have hEq : X.1.1 = Y.1.1 := by simpa [f] using hval
          have hN : X.1.1 ∈ lineNeighbors c := hEq.symm ▸ Y.1.2
          exact firstCase_rootLayerTwo_not_lineNeighbor
            hmin c hfirst d X.1.1 X.1.2 hN
        · rcases Y with Y | Y
          · congr 2
            apply Subtype.ext
            apply Subtype.ext
            have hval := congrArg Subtype.val hXY
            simpa [f] using hval
          · exfalso
            have hval := congrArg Subtype.val hXY
            have hEq : X.1.1 = Y.1.1 := by simpa [f] using hval
            have hT : Y.1.1 ∈ firstCaseRootLayerTwo hmin c hfirst := hEq ▸ X.1.2
            exact firstCase_rootLayerTwo_not_rootLayerFour
              hmin c hfirst Y.1.1 hT Y.1.2
      · rcases Y with Y | Y
        · exfalso
          have hval := congrArg Subtype.val hXY
          have hEq : X.1.1 = Y.1.1 := by simpa [f] using hval
          have hN : X.1.1 ∈ lineNeighbors c := hEq.symm ▸ Y.1.2
          exact firstCase_rootLayerFour_not_lineNeighbor
            hmin c hfirst d X.1.1 X.1.2 hN
        · rcases Y with Y | Y
          · exfalso
            have hval := congrArg Subtype.val hXY
            have hEq : X.1.1 = Y.1.1 := by simpa [f] using hval
            have hT : X.1.1 ∈ firstCaseRootLayerTwo hmin c hfirst := hEq.symm ▸ Y.1.2
            exact firstCase_rootLayerTwo_not_rootLayerFour
              hmin c hfirst X.1.1 hT X.1.2
          · congr 2
            apply Subtype.ext
            apply Subtype.ext
            have hval := congrArg Subtype.val hXY
            simpa [f] using hval
  have hle := Nat.card_le_card_of_injective f hf
  have hN0 : Nat.card N0 = 1 :=
    firstCase_rootLayerFour_rootNeighbor_card_one hmin c hfirst d V hV
  have hT0 : Nat.card T0 = 3 :=
    (firstCase_rootLayerFour_two_incidence hmin c hfirst d).1 V hV
  have hFull : Nat.card Full = 4 :=
    firstCase_commutingGraph_degree_four hmin c hfirst d V
  have hF0 : Nat.card F0 =
      Nat.card {W : {W : UConjugates c //
        W ∈ firstCaseRootLayerFour hmin c hfirst} //
          (commutingGraph c).Adj V W.1} := rfl
  rw [Nat.card_sum, Nat.card_sum, hN0, hT0, hFull, hF0] at hle
  omega

/-- Every fibre-two vertex has two neighbours in its own layer; its other two
neighbours lie in the fibre-four layer. -/
public theorem firstCase_rootLayerTwo_internal_neighbors_card_two
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c) (V : UConjugates c)
    (hV : V ∈ firstCaseRootLayerTwo hmin c hfirst) :
    Nat.card {W : {W : UConjugates c //
      W ∈ firstCaseRootLayerTwo hmin c hfirst} //
        (commutingGraph c).Adj V W.1} = 2 := by
  classical
  let F := {W : UConjugates c // W ∈ firstCaseRootLayerFour hmin c hfirst}
  let T := {W : UConjugates c // W ∈ firstCaseRootLayerTwo hmin c hfirst}
  let FT := {W : F // (commutingGraph c).Adj W.1 V}
  let TT := {W : T // (commutingGraph c).Adj V W.1}
  let Full := {W : UConjugates c // (commutingGraph c).Adj V W}
  let f : Full → Sum FT TT := fun W =>
    if hF : W.1 ∈ firstCaseRootLayerFour hmin c hfirst then
      Sum.inl ⟨⟨W.1, hF⟩, W.2.symm⟩
    else
      Sum.inr ⟨⟨W.1, by
        rcases firstCase_root_partition hmin c hfirst d W.1 with
          hbase | hN | hT | hF'
        · exact False.elim (firstCase_rootLayerTwo_not_adjacent_base
            hmin c hfirst d V hV (by simpa [hbase] using W.2))
        · let WN : lineNeighborSet c := ⟨W.1, hN⟩
          exact False.elim (firstCase_rootNeighbor_not_adjacent_rootLayerTwo
            hmin c hfirst d WN V hV W.2.symm)
        · exact hT
        · exact False.elim (hF hF')⟩, W.2⟩
  let g : Sum FT TT → Full
    | Sum.inl W => ⟨W.1.1, W.2.symm⟩
    | Sum.inr W => ⟨W.1.1, W.2⟩
  have hgf : Function.LeftInverse g f := by
    intro W
    dsimp [f]
    split_ifs <;> rfl
  have hfg : Function.RightInverse g f := by
    intro W
    rcases W with W | W
    · dsimp [f, g]
      simp [W.1.2]
    · dsimp [f, g]
      have hnot : W.1.1 ∉ firstCaseRootLayerFour hmin c hfirst := by
        intro hF
        exact firstCase_rootLayerTwo_not_rootLayerFour
          hmin c hfirst W.1.1 W.1.2 hF
      simp [hnot]
  let e : Full ≃ Sum FT TT := Equiv.ofBijective f
    ⟨hgf.injective, hfg.surjective⟩
  have hFull : Nat.card Full = 4 :=
    firstCase_commutingGraph_degree_four hmin c hfirst d V
  have hFT : Nat.card FT = 2 :=
    (firstCase_rootLayerFour_two_incidence hmin c hfirst d).2 V hV
  have hsplit : Nat.card Full = Nat.card FT + Nat.card TT := by
    calc
      Nat.card Full = Nat.card (Sum FT TT) := Nat.card_congr e
      _ = Nat.card FT + Nat.card TT := Nat.card_sum
  rw [hFull, hFT] at hsplit
  change Nat.card TT = 2
  omega

end CFSG.GorensteinWalter
