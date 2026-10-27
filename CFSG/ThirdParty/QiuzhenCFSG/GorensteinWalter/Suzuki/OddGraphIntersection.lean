module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphOrbitals
public import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The first rooted intersection fact

The rooted non-base vertices split into the fibre-two and fibre-four layers.
This module records their vertex-set cardinalities and proves that no graph
edge joins a root neighbour to the fibre-two layer.  The latter is a small
incidence count: the fibre-two layer is a single `Ĥ`-orbit, so the incidence
fibres on that side all have the same cardinality, while the four root
neighbours have total degree four.
-/

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

@[expose] public def firstCaseRootLayerTwo
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G) (c : CentralizerSetup G)
    (hfirst : FirstCase c) : Set (UConjugates c) :=
  {V | (cosetLineEquiv hmin c hfirst).symm V ≠ cosetInvolution_base c.Hhat ∧
    Nat.card (cosetInvolution_fiber c.Hhat
      ((cosetLineEquiv hmin c hfirst).symm V)) = 2}

@[expose] public def firstCaseRootLayerFour
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G) (c : CentralizerSetup G)
    (hfirst : FirstCase c) : Set (UConjugates c) :=
  {V | (cosetLineEquiv hmin c hfirst).symm V ≠ cosetInvolution_base c.Hhat ∧
    Nat.card (cosetInvolution_fiber c.Hhat
      ((cosetLineEquiv hmin c hfirst).symm V)) = 4}

public theorem firstCaseRootLayerTwo_card
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c) :
    Nat.card {V : UConjugates c // V ∈ firstCaseRootLayerTwo hmin c hfirst} = 18 := by
  let e := cosetLineEquiv hmin c hfirst
  let f : firstCaseCosetLayer c 2 ≃
      {V : UConjugates c // V ∈ firstCaseRootLayerTwo hmin c hfirst} :=
    { toFun := fun q => ⟨e q.1, by
        change e.symm (e q.1) ≠ _ ∧ _
        rw [e.symm_apply_apply]
        exact q.2⟩
      invFun := fun V => ⟨e.symm V.1, by
        change e.symm V.1 ≠ _ ∧ _
        exact V.2⟩
      left_inv := by intro q; apply Subtype.ext; simp
      right_inv := by intro V; apply Subtype.ext; simp }
  calc
    Nat.card {V : UConjugates c // V ∈ firstCaseRootLayerTwo hmin c hfirst} =
        Nat.card (firstCaseCosetLayer c 2) := (Nat.card_congr f).symm
    _ = 18 := (firstCaseCosetLayer_card hmin c hfirst d).2.1

public theorem firstCaseRootLayerFour_card
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c) :
    Nat.card {V : UConjugates c // V ∈ firstCaseRootLayerFour hmin c hfirst} = 12 := by
  let e := cosetLineEquiv hmin c hfirst
  let f : firstCaseCosetLayer c 4 ≃
      {V : UConjugates c // V ∈ firstCaseRootLayerFour hmin c hfirst} :=
    { toFun := fun q => ⟨e q.1, by
        change e.symm (e q.1) ≠ _ ∧ _
        rw [e.symm_apply_apply]
        exact q.2⟩
      invFun := fun V => ⟨e.symm V.1, by
        change e.symm V.1 ≠ _ ∧ _
        exact V.2⟩
      left_inv := by intro q; apply Subtype.ext; simp
      right_inv := by intro V; apply Subtype.ext; simp }
  calc
    Nat.card {V : UConjugates c // V ∈ firstCaseRootLayerFour hmin c hfirst} =
        Nat.card (firstCaseCosetLayer c 4) := (Nat.card_congr f).symm
    _ = 12 := (firstCaseCosetLayer_card hmin c hfirst d).2.2

public theorem firstCaseRootLayerTwo_transitive
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c)
    {V W : UConjugates c}
    (hV : V ∈ firstCaseRootLayerTwo hmin c hfirst)
    (hW : W ∈ firstCaseRootLayerTwo hmin c hfirst) :
    ∃ h : c.Hhat, (h : G) • V = W := by
  let e := cosetLineEquiv hmin c hfirst
  have hqV : (e.symm V) ≠ cosetInvolution_base c.Hhat ∧
      Nat.card (cosetInvolution_fiber c.Hhat (e.symm V)) = 2 := hV
  have hqW : (e.symm W) ≠ cosetInvolution_base c.Hhat ∧
      Nat.card (cosetInvolution_fiber c.Hhat (e.symm W)) = 2 := hW
  have horb := firstCaseCosetLayer_two_orbit_eq hmin c hfirst d (e.symm V) hqV
  have hmem : e.symm W ∈ MulAction.orbit c.Hhat (e.symm V) := by
    rw [horb]
    exact hqW
  rcases hmem with ⟨h, hh⟩
  refine ⟨h, ?_⟩
  have hh' : (h : G) • e.symm V = e.symm W := hh
  calc
    (h : G) • V = (h : G) • e (e.symm V) := by
      rw [e.apply_symm_apply]
    _ = e ((h : G) • e.symm V) := by
      rw [cosetLineEquiv_smul]
    _ = e (e.symm W) := by rw [hh']
    _ = W := e.apply_symm_apply W

public theorem firstCaseRootLayerFour_transitive
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c)
    {V W : UConjugates c}
    (hV : V ∈ firstCaseRootLayerFour hmin c hfirst)
    (hW : W ∈ firstCaseRootLayerFour hmin c hfirst) :
    ∃ h : c.Hhat, (h : G) • V = W := by
  let e := cosetLineEquiv hmin c hfirst
  have hqV : (e.symm V) ≠ cosetInvolution_base c.Hhat ∧
      Nat.card (cosetInvolution_fiber c.Hhat (e.symm V)) = 4 := hV
  have hqW : (e.symm W) ≠ cosetInvolution_base c.Hhat ∧
      Nat.card (cosetInvolution_fiber c.Hhat (e.symm W)) = 4 := hW
  have horb := firstCaseCosetLayer_four_orbit_eq hmin c hfirst d (e.symm V) hqV
  have hmem : e.symm W ∈ MulAction.orbit c.Hhat (e.symm V) := by
    rw [horb]
    exact hqW
  rcases hmem with ⟨h, hh⟩
  refine ⟨h, ?_⟩
  have hh' : (h : G) • e.symm V = e.symm W := hh
  calc
    (h : G) • V = (h : G) • e (e.symm V) := by
      rw [e.apply_symm_apply]
    _ = e ((h : G) • e.symm V) := by
      rw [cosetLineEquiv_smul]
    _ = e (e.symm W) := by rw [hh']
    _ = W := e.apply_symm_apply W

/-- Every vertex of the commuting graph has degree four. -/
public theorem firstCase_commutingGraph_degree_four
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c) (V : UConjugates c) :
    Nat.card {W : UConjugates c // (commutingGraph c).Adj V W} = 4 := by
  rcases V.2 with ⟨g, hV⟩
  let V' : UConjugates c := g • UConjugates.base c
  have hV' : V' = V := by
    apply Subtype.ext
    change conjugateSubgroup c.U g = V.1
    exact hV.symm
  let f : {W : UConjugates c // (commutingGraph c).Adj
      (UConjugates.base c) W} →
      {W : UConjugates c // (commutingGraph c).Adj V' W} := fun W =>
    ⟨g • W.1, by
      have h := (commutingGraph.adj_smul_iff c g
        (UConjugates.base c) W.1).mpr W.2
      simpa [V'] using h⟩
  have hf : Function.Bijective f := by
    constructor
    · intro A B hAB
      apply Subtype.ext
      have hAB' : g • A.1 = g • B.1 := congrArg Subtype.val hAB
      have h' := congrArg (fun X : UConjugates c => g⁻¹ • X) hAB'
      simpa [← mul_smul] using h'
    · intro W
      let X : UConjugates c := g⁻¹ • W.1
      have hX : (commutingGraph c).Adj (UConjugates.base c) X := by
        have h := (commutingGraph.adj_smul_iff c g⁻¹
          V' W.1).mpr W.2
        simpa [V', X, ← mul_smul] using h
      refine ⟨⟨X, hX⟩, ?_⟩
      apply Subtype.ext
      dsimp [f, X]
      simp [← mul_smul]
  have hcard : Nat.card {W : UConjugates c // (commutingGraph c).Adj V' W} =
      Nat.card {W : UConjugates c // (commutingGraph c).Adj
        (UConjugates.base c) W} := (Nat.card_congr (Equiv.ofBijective f hf)).symm
  rw [← hV', hcard]
  have eA : {W : UConjugates c // (commutingGraph c).Adj
      (UConjugates.base c) W} ≃ lineNeighborSet c :=
    { toFun := fun W => ⟨W.1, by
          have h := (commutingGraph_adj_iff c (UConjugates.base c) W.1).mp W.2
          exact ⟨h.1.symm, h.2⟩⟩
      invFun := fun W => ⟨W.1, by
          exact (commutingGraph_adj_iff c (UConjugates.base c) W.1).mpr
            ⟨W.2.1.symm, W.2.2⟩⟩
      left_inv := by intro W; rfl
      right_inv := by intro W; rfl }
  calc
    Nat.card {W : UConjugates c // (commutingGraph c).Adj
        (UConjugates.base c) W} = Nat.card (lineNeighborSet c) :=
      Nat.card_congr eA
    _ = 4 := neighbor_card_eq_four hmin c hfirst d

public def firstCase_rootNeighbor_smul
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (h : c.Hhat) (V : lineNeighborSet c) : lineNeighborSet c := by
  have hfix : (h : G) • UConjugates.base c = UConjugates.base c := by
    apply MulAction.mem_stabilizer_iff.mp
    rw [commutingGraph.stabilizer_base_eq_hhat hmin c hfirst]
    exact h.2
  have hAdj : (commutingGraph c).Adj (UConjugates.base c) V.1 :=
    (commutingGraph_adj_iff c _ _).mpr ⟨V.2.1.symm, V.2.2⟩
  have hAdj' : (commutingGraph c).Adj (UConjugates.base c) ((h : G) • V.1) := by
    have h' := (commutingGraph.adj_smul_iff c (h : G)
      (UConjugates.base c) V.1).mpr hAdj
    simpa [hfix] using h'
  have hAdj'' := (commutingGraph_adj_iff c _ _).mp hAdj'
  exact ⟨(h : G) • V.1, ⟨hAdj''.1.symm, hAdj''.2⟩⟩

public theorem firstCase_rootNeighbor_smul_val
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (h : c.Hhat) (V : lineNeighborSet c) :
    (firstCase_rootNeighbor_smul hmin c hfirst h V : UConjugates c) =
      (h : G) • V.1 := by simp [firstCase_rootNeighbor_smul]

public theorem firstCase_rootNeighbor_smul_inv
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (h : c.Hhat) (V : lineNeighborSet c) :
    firstCase_rootNeighbor_smul hmin c hfirst (h⁻¹)
        (firstCase_rootNeighbor_smul hmin c hfirst h V) = V := by
  apply Subtype.ext
  dsimp [firstCase_rootNeighbor_smul]
  rw [← mul_smul]
  simp

private def rootTwo_incidence_equiv
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    {V W : UConjugates c}
    (hV : V ∈ firstCaseRootLayerTwo hmin c hfirst)
    (hW : W ∈ firstCaseRootLayerTwo hmin c hfirst)
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

private theorem rootTwo_incidence_empty
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c) :
    ∀ V : lineNeighborSet c, ∀ W : UConjugates c,
      W ∈ firstCaseRootLayerTwo hmin c hfirst →
      ¬ (commutingGraph c).Adj V.1 W := by
  classical
  let A := lineNeighborSet c
  let B := {W : UConjugates c // W ∈ firstCaseRootLayerTwo hmin c hfirst}
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
  have hIle : Nat.card I ≤ 16 := by
    have hle (V : A) : Nat.card {W : B // (commutingGraph c).Adj V.1 W.1} ≤
        Nat.card {W : UConjugates c // (commutingGraph c).Adj V.1 W} := by
      let f : {W : B // (commutingGraph c).Adj V.1 W.1} →
          {W : UConjugates c // (commutingGraph c).Adj V.1 W} := fun W =>
        ⟨W.1, W.2⟩
      exact Nat.card_le_card_of_injective f (by
        intro X Y hXY
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun Z => Z.1) hXY)
    rw [hIcardA]
    calc
      (∑ V : A, Nat.card {W : B // (commutingGraph c).Adj V.1 W.1}) ≤
          ∑ V : A, Nat.card {W : UConjugates c //
            (commutingGraph c).Adj V.1 W} := Finset.sum_le_sum (fun V _ => hle V)
      _ = ∑ _V : A, 4 := by
        apply Finset.sum_congr rfl
        intro V _
        exact firstCase_commutingGraph_degree_four hmin c hfirst d V.1
      _ = 16 := by
        rw [Finset.sum_const, Finset.card_univ]
        have hA : Nat.card A = 4 := neighbor_card_eq_four hmin c hfirst d
        have hA' : Fintype.card A = 4 := by
          simpa [Nat.card_eq_fintype_card] using hA
        simp [hA']
  have hBcard : Nat.card B = 18 := firstCaseRootLayerTwo_card hmin c hfirst d
  have hBcard' : Fintype.card B = 18 := by
    simpa [Nat.card_eq_fintype_card] using hBcard
  obtain ⟨W0⟩ := (Nat.card_pos_iff.mp (by omega : 0 < Nat.card B)).1
  let k : ℕ := Nat.card {V : A // (commutingGraph c).Adj V.1 W0.1}
  have hconst (W : B) : Nat.card {V : A // (commutingGraph c).Adj V.1 W.1} = k := by
    obtain ⟨h, hVW⟩ := firstCaseRootLayerTwo_transitive hmin c hfirst d
      (V := W0.1) (W := W.1) W0.2 W.2
    let e := rootTwo_incidence_equiv hmin c hfirst
      (V := W0.1) (W := W.1) W0.2 W.2 h hVW
    exact (Nat.card_congr e).symm
  have hdiv : 18 ∣ Nat.card I := by
    refine ⟨k, ?_⟩
    rw [hIcardB]
    simp_rw [hconst]
    simp [k, hBcard']
  obtain ⟨m, hm⟩ := hdiv
  have hIle' : Nat.card I ≤ 16 := by simpa [Nat.card_eq_fintype_card] using hIle
  have hmle : 18 * m ≤ 16 := by rw [← hm]; exact hIle'
  have hm0 : m = 0 := by omega
  have hI0 : Nat.card I = 0 := by simpa [hm0] using hm
  intro V W hW hAdj
  let p : I := ⟨⟨V, ⟨W, hW⟩⟩, hAdj⟩
  have hp : 0 < Nat.card I := Nat.card_pos_iff.mpr ⟨Nonempty.intro p, inferInstance⟩
  omega

/-- A root neighbour has no edge to a fibre-two vertex. -/
public theorem firstCase_rootNeighbor_not_adjacent_rootLayerTwo
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c)
    (V : lineNeighborSet c) (W : UConjugates c)
    (hW : W ∈ firstCaseRootLayerTwo hmin c hfirst) :
    ¬ (commutingGraph c).Adj V.1 W :=
  rootTwo_incidence_empty hmin c hfirst d V W hW

end CFSG.GorensteinWalter
