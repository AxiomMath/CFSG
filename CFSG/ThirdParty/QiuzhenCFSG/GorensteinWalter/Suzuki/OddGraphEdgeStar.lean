module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphSpectrum
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Intrinsic edge stars in the Suzuki commuting graph

Every edge determines a fifteen-vertex coclique: the three remaining
neighbours at each endpoint together with the nine vertices at distance three
from both endpoints.  The spectral equality case shows that this coclique is
the unique fifteen-point independent set avoiding both endpoints.
-/

namespace CFSG.GorensteinWalter

universe u

noncomputable section

@[expose] public def commutingGraphEdgeWing
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (A B : UConjugates c) :
    Set (UConjugates c) :=
  {X | (commutingGraph c).Adj A X ∧ X ≠ B}

@[expose] public def commutingGraphEdgeCenter
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (A B : UConjugates c) :
    Set (UConjugates c) :=
  {X | commutingGraphDistThree c A X ∧ commutingGraphDistThree c B X}

@[expose] public def commutingGraphEdgeStar
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (A B : UConjugates c) :
    Set (UConjugates c) :=
  commutingGraphEdgeWing c A B ∪ commutingGraphEdgeWing c B A ∪ commutingGraphEdgeCenter c A B

private def edgeThreeTwoCell
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (A B : UConjugates c) :
    Set (UConjugates c) :=
  {X | commutingGraphDistThree c A X ∧ commutingGraphDistTwo c B X}

private theorem commutingGraphEdgeWing_distTwo_other
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c)
    {A B X : UConjugates c}
    (hAB : (commutingGraph c).Adj A B)
    (hX : X ∈ commutingGraphEdgeWing c A B) :
    commutingGraphDistTwo c B X := by
  refine ⟨hX.2.symm, ?_, ?_⟩
  · exact firstCase_commutingGraph_triangle_free
      hmin c hfirst d hAB hX.1
  · exact ⟨A, hAB.symm, hX.1⟩

public theorem firstCase_no_distTwo_both_edge_endpoints
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c)
    {A B X : UConjugates c}
    (hAB : (commutingGraph c).Adj A B)
    (hAX : commutingGraphDistTwo c A X)
    (hBX : commutingGraphDistTwo c B X) : False := by
  obtain ⟨Q, hBQ, hQX⟩ := hBX.2.2
  have hQA : Q ≠ A := by
    intro hQA
    apply hAX.2.1
    simpa only [hQA] using hQX
  have hAQ : ¬ (commutingGraph c).Adj A Q :=
    firstCase_commutingGraph_triangle_free
      hmin c hfirst d hAB.symm hBQ
  have hQdist : commutingGraphDistTwo c A Q :=
    ⟨hQA.symm, hAQ, ⟨B, hAB, hBQ⟩⟩
  exact firstCase_distTwo_not_adjacent
    hmin c hfirst d hQdist hAX hQX

public theorem firstCase_edgeWing_ncard_three
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c)
    {A B : UConjugates c}
    (hAB : (commutingGraph c).Adj A B) :
    (commutingGraphEdgeWing c A B).ncard = 3 := by
  let N : Set (UConjugates c) := {X | (commutingGraph c).Adj A X}
  have hN : N.ncard = 4 := by
    change Nat.card {X : UConjugates c // (commutingGraph c).Adj A X} = 4
    exact firstCase_commutingGraph_degree_four hmin c hfirst d A
  have hmem : B ∈ N := hAB
  have hEq : commutingGraphEdgeWing c A B = N \ {B} := by
    ext X
    simp only [commutingGraphEdgeWing, N, Set.mem_setOf_eq, Set.mem_sdiff,
      Set.mem_singleton_iff]
  rw [hEq, Set.ncard_sdiff_singleton_of_mem hmem, hN]

private theorem edgeThreeTwoCell_ncard_nine
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c)
    {A B : UConjugates c}
    (hAB : (commutingGraph c).Adj A B) :
    (edgeThreeTwoCell c A B).ncard = 9 := by
  let L : Set (UConjugates c) :=
    {X | commutingGraphDistTwo c B X}
  have hpartition : L = commutingGraphEdgeWing c A B ∪ edgeThreeTwoCell c A B := by
    ext X
    constructor
    · intro hBX
      by_cases hAX : (commutingGraph c).Adj A X
      · exact Or.inl ⟨hAX, hBX.1.symm⟩
      · right
        refine ⟨⟨?_, hAX, ?_⟩, hBX⟩
        · intro hAXeq
          apply hBX.2.1
          simpa only [hAXeq] using hAB.symm
        · intro hcommon
          exact firstCase_no_distTwo_both_edge_endpoints hmin c hfirst d hAB
            ⟨by
              intro hAXeq
              apply hBX.2.1
              simpa only [hAXeq] using hAB.symm,
             hAX, hcommon⟩ hBX
    · rintro (hwing | hcell)
      · exact commutingGraphEdgeWing_distTwo_other hmin c hfirst d hAB hwing
      · exact hcell.2
  have hdisjoint : Disjoint (commutingGraphEdgeWing c A B) (edgeThreeTwoCell c A B) := by
    refine Set.disjoint_left.2 ?_
    intro X hwing hcell
    exact hcell.1.2.1 hwing.1
  have hL : L.ncard = 12 := by
    change Nat.card {X : UConjugates c // commutingGraphDistTwo c B X} = 12
    exact firstCase_distTwo_layer_card hmin c hfirst d B
  rw [hpartition, Set.ncard_union_eq hdisjoint,
    firstCase_edgeWing_ncard_three hmin c hfirst d hAB] at hL
  omega

public theorem firstCase_edgeCenter_ncard_nine
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c)
    {A B : UConjugates c}
    (hAB : (commutingGraph c).Adj A B) :
    (commutingGraphEdgeCenter c A B).ncard = 9 := by
  let T : Set (UConjugates c) :=
    {X | commutingGraphDistThree c A X}
  have hpartition :
      T = edgeThreeTwoCell c A B ∪ commutingGraphEdgeCenter c A B := by
    ext X
    constructor
    · intro hAX
      by_cases hcommon : commutingGraphHasCommonNeighbor c B X
      · left
        refine ⟨hAX, ?_⟩
        refine ⟨?_, ?_, hcommon⟩
        · intro hBXeq
          apply hAX.2.1
          simpa only [hBXeq] using hAB
        · intro hBX
          exact hAX.2.2 ⟨B, hAB, hBX⟩
      · right
        refine ⟨hAX, ?_⟩
        refine ⟨?_, ?_, hcommon⟩
        · intro hBXeq
          apply hAX.2.1
          simpa only [hBXeq] using hAB
        · intro hBX
          exact hAX.2.2 ⟨B, hAB, hBX⟩
    · rintro (hcell | hcenter)
      · exact hcell.1
      · exact hcenter.1
  have hdisjoint :
      Disjoint (edgeThreeTwoCell c A B) (commutingGraphEdgeCenter c A B) := by
    refine Set.disjoint_left.2 ?_
    intro X hcell hcenter
    exact hcenter.2.2.2 hcell.2.2.2
  have hT : T.ncard = 18 := by
    change Nat.card {X : UConjugates c // commutingGraphDistThree c A X} = 18
    exact firstCase_distThree_layer_card hmin c hfirst d A
  rw [hpartition, Set.ncard_union_eq hdisjoint,
    edgeThreeTwoCell_ncard_nine hmin c hfirst d hAB] at hT
  omega

public theorem firstCase_edgeStar_ncard_fifteen
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c)
    {A B : UConjugates c}
    (hAB : (commutingGraph c).Adj A B) :
    (commutingGraphEdgeStar c A B).ncard = 15 := by
  have hLR : Disjoint (commutingGraphEdgeWing c A B) (commutingGraphEdgeWing c B A) := by
    refine Set.disjoint_left.2 ?_
    intro X hL hR
    exact (firstCase_commutingGraph_triangle_free
      hmin c hfirst d hAB hL.1) hR.1
  have hLRC :
      Disjoint (commutingGraphEdgeWing c A B ∪ commutingGraphEdgeWing c B A) (commutingGraphEdgeCenter c A B) := by
    refine Set.disjoint_left.2 ?_
    intro X hW hC
    rcases hW with hL | hR
    · exact hC.1.2.1 hL.1
    · exact hC.2.2.1 hR.1
  rw [commutingGraphEdgeStar, Set.ncard_union_eq hLRC, Set.ncard_union_eq hLR,
    firstCase_edgeWing_ncard_three hmin c hfirst d hAB,
    firstCase_edgeWing_ncard_three hmin c hfirst d hAB.symm,
    firstCase_edgeCenter_ncard_nine hmin c hfirst d hAB]

private def distTwoNeighbors
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (A X : UConjugates c) :
    Set (UConjugates c) :=
  {Y | commutingGraphDistTwo c A Y ∧ (commutingGraph c).Adj X Y}

private theorem distTwoNeighbors_ncard_two
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c)
    {A X : UConjugates c}
    (hX : commutingGraphDistThree c A X) :
    (distTwoNeighbors c A X).ncard = 2 := by
  let e :
      {Y : {Y : UConjugates c // commutingGraphDistTwo c A Y} //
        (commutingGraph c).Adj X Y.1} ≃
      {Y : UConjugates c //
        commutingGraphDistTwo c A Y ∧ (commutingGraph c).Adj X Y} :=
    { toFun := fun Y => ⟨Y.1.1, ⟨Y.1.2, Y.2⟩⟩
      invFun := fun Y => ⟨⟨Y.1, Y.2.1⟩, Y.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc
    (distTwoNeighbors c A X).ncard =
        Nat.card {Y : {Y : UConjugates c // commutingGraphDistTwo c A Y} //
          (commutingGraph c).Adj X Y.1} := by
      change Nat.card {Y : UConjugates c //
        commutingGraphDistTwo c A Y ∧ (commutingGraph c).Adj X Y} = _
      exact (Nat.card_congr e).symm
    _ = 2 := firstCase_distThree_distTwo_neighbors_card_two
      hmin c hfirst d A X hX

private theorem commutingGraphEdgeCenter_not_adjacent
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c)
    {A B X Y : UConjugates c}
    (hAB : (commutingGraph c).Adj A B)
    (hX : X ∈ commutingGraphEdgeCenter c A B)
    (hY : Y ∈ commutingGraphEdgeCenter c A B) :
    ¬ (commutingGraph c).Adj X Y := by
  intro hXY
  let DA := distTwoNeighbors c A X
  let DB := distTwoNeighbors c B X
  have hDADisjDB : Disjoint DA DB := by
    refine Set.disjoint_left.2 ?_
    intro Z hZA hZB
    exact firstCase_no_distTwo_both_edge_endpoints
      hmin c hfirst d hAB hZA.1 hZB.1
  have hYnotDA : Y ∉ DA := by
    intro hYA
    exact hY.1.2.2 hYA.1.2.2
  have hYnotDB : Y ∉ DB := by
    intro hYB
    exact hY.2.2.2 hYB.1.2.2
  have hUnionDisjY : Disjoint (DA ∪ DB) ({Y} : Set (UConjugates c)) := by
    refine Set.disjoint_left.2 ?_
    intro Z hZ hZY
    have hZYeq : Z = Y := by simpa only [Set.mem_singleton_iff] using hZY
    subst Z
    rcases hZ with hYA | hYB
    · exact hYnotDA hYA
    · exact hYnotDB hYB
  have hDA : DA.ncard = 2 :=
    distTwoNeighbors_ncard_two hmin c hfirst d hX.1
  have hDB : DB.ncard = 2 :=
    distTwoNeighbors_ncard_two hmin c hfirst d hX.2
  have hlarge : ((DA ∪ DB) ∪ ({Y} : Set (UConjugates c))).ncard = 5 := by
    rw [Set.ncard_union_eq hUnionDisjY, Set.ncard_union_eq hDADisjDB,
      hDA, hDB, Set.ncard_singleton]
  let N : Set (UConjugates c) := {Z | (commutingGraph c).Adj X Z}
  have hsubset : (DA ∪ DB) ∪ ({Y} : Set (UConjugates c)) ⊆ N := by
    intro Z hZ
    rcases hZ with (hZA | hZB) | hZY
    · exact hZA.2
    · exact hZB.2
    · have hZYeq : Z = Y := by
        simpa only [Set.mem_singleton_iff] using hZY
      subst Z
      exact hXY
  have hN : N.ncard = 4 := by
    change Nat.card {Z : UConjugates c // (commutingGraph c).Adj X Z} = 4
    exact firstCase_commutingGraph_degree_four hmin c hfirst d X
  have hle := Set.ncard_le_ncard hsubset
  rw [hlarge, hN] at hle
  omega

private theorem commutingGraphEdgeWings_not_adjacent
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c)
    {A B X Y : UConjugates c}
    (hAB : (commutingGraph c).Adj A B)
    (hX : X ∈ commutingGraphEdgeWing c A B)
    (hY : Y ∈ commutingGraphEdgeWing c B A) :
    ¬ (commutingGraph c).Adj X Y := by
  intro hXY
  have hEq : A = Y :=
    firstCase_commutingGraph_commonNeighbor_unique
      hmin c hfirst d hX.2.symm hAB.symm hX.1 hY.1 hXY.symm
  exact hY.2 hEq.symm

private theorem commutingGraphEdgeWing_center_not_adjacent
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    {A B X Y : UConjugates c}
    (hX : X ∈ commutingGraphEdgeWing c A B)
    (hY : Y ∈ commutingGraphEdgeCenter c A B) :
    ¬ (commutingGraph c).Adj X Y := by
  intro hXY
  exact hY.1.2.2 ⟨X, hX.1, hXY⟩

public theorem firstCase_edgeStar_isIndepSet
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c)
    {A B : UConjugates c}
    (hAB : (commutingGraph c).Adj A B) :
    (commutingGraph c).IsIndepSet (commutingGraphEdgeStar c A B) := by
  intro X hXS Y hYS _
  change X ∈ commutingGraphEdgeWing c A B ∪ commutingGraphEdgeWing c B A ∪ commutingGraphEdgeCenter c A B at hXS
  change Y ∈ commutingGraphEdgeWing c A B ∪ commutingGraphEdgeWing c B A ∪ commutingGraphEdgeCenter c A B at hYS
  rcases hXS with (hXL | hXR) | hXC
  · rcases hYS with (hYL | hYR) | hYC
    · exact firstCase_commutingGraph_triangle_free
        hmin c hfirst d hXL.1 hYL.1
    · exact commutingGraphEdgeWings_not_adjacent hmin c hfirst d hAB hXL hYR
    · exact commutingGraphEdgeWing_center_not_adjacent c hXL hYC
  · rcases hYS with (hYL | hYR) | hYC
    · intro hXY
      exact commutingGraphEdgeWings_not_adjacent hmin c hfirst d hAB hYL hXR hXY.symm
    · exact firstCase_commutingGraph_triangle_free
        hmin c hfirst d hXR.1 hYR.1
    · exact commutingGraphEdgeWing_center_not_adjacent c hXR ⟨hYC.2, hYC.1⟩
  · rcases hYS with (hYL | hYR) | hYC
    · intro hXY
      exact commutingGraphEdgeWing_center_not_adjacent c hYL hXC hXY.symm
    · intro hXY
      exact commutingGraphEdgeWing_center_not_adjacent c hYR ⟨hXC.2, hXC.1⟩ hXY.symm
    · exact commutingGraphEdgeCenter_not_adjacent hmin c hfirst d hAB hXC hYC

public theorem commutingGraphEdgeStar_endpoints_not_mem
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (A B : UConjugates c) :
    A ∉ commutingGraphEdgeStar c A B ∧ B ∉ commutingGraphEdgeStar c A B := by
  constructor
  · rintro ((hAA | hBA) | hCA)
    · exact (commutingGraph c).irrefl hAA.1
    · exact hBA.2 rfl
    · exact hCA.1.1 rfl
  · rintro ((hAB | hBB) | hCB)
    · exact hAB.2 rfl
    · exact (commutingGraph c).irrefl hBB.1
    · exact hCB.2.1 rfl

public theorem commutingGraphEdgeStar_comm
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (A B : UConjugates c) :
    commutingGraphEdgeStar c A B = commutingGraphEdgeStar c B A := by
  ext X
  simp only [commutingGraphEdgeStar, commutingGraphEdgeWing, commutingGraphEdgeCenter, Set.mem_union,
    Set.mem_setOf_eq]
  aesop

public theorem commutingGraphEdgeStar_smul_iff
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (g : G) (A B X : UConjugates c) :
    g • X ∈ commutingGraphEdgeStar c (g • A) (g • B) ↔ X ∈ commutingGraphEdgeStar c A B := by
  simp only [commutingGraphEdgeStar, commutingGraphEdgeWing, commutingGraphEdgeCenter, Set.mem_union,
    Set.mem_setOf_eq, commutingGraph.adj_smul_iff,
    commutingGraphDistThree_smul_iff, ne_eq]
  constructor
  · rintro ((hAX | hBX) | hCX)
    · exact Or.inl (Or.inl ⟨hAX.1, fun h => hAX.2 (congrArg (fun Y => g • Y) h)⟩)
    · exact Or.inl (Or.inr ⟨hBX.1, fun h => hBX.2 (congrArg (fun Y => g • Y) h)⟩)
    · exact Or.inr hCX
  · rintro ((hAX | hBX) | hCX)
    · exact Or.inl (Or.inl ⟨hAX.1, (MulAction.injective g).ne hAX.2⟩)
    · exact Or.inl (Or.inr ⟨hBX.1, (MulAction.injective g).ne hBX.2⟩)
    · exact Or.inr hCX

public theorem firstCase_edgeStar_unique
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c)
    {A B : UConjugates c}
    (hAB : (commutingGraph c).Adj A B)
    (S : Set (UConjugates c))
    (hS : (commutingGraph c).IsIndepSet S)
    (hcard : S.ncard = 15)
    (hA : A ∉ S) (hB : B ∉ S) :
    S = commutingGraphEdgeStar c A B := by
  classical
  let := Fintype.ofFinite (UConjugates c)
  let SA : Set (UConjugates c) :=
    {X | X ∈ S ∧ (commutingGraph c).Adj A X}
  let SB : Set (UConjugates c) :=
    {X | X ∈ S ∧ (commutingGraph c).Adj B X}
  have hSAcard : SA.ncard = 3 := by
    change Nat.card {X : UConjugates c //
      X ∈ S ∧ (commutingGraph c).Adj A X} = 3
    exact firstCase_indepSet_card_fifteen_outside_neighbors
      hmin c hfirst d S hS hcard A hA
  have hSBcard : SB.ncard = 3 := by
    change Nat.card {X : UConjugates c //
      X ∈ S ∧ (commutingGraph c).Adj B X} = 3
    exact firstCase_indepSet_card_fifteen_outside_neighbors
      hmin c hfirst d S hS hcard B hB
  have hSAsub : SA ⊆ commutingGraphEdgeWing c A B := by
    intro X hX
    refine ⟨hX.2, ?_⟩
    intro hXB
    apply hB
    simpa only [hXB] using hX.1
  have hSBsub : SB ⊆ commutingGraphEdgeWing c B A := by
    intro X hX
    refine ⟨hX.2, ?_⟩
    intro hXA
    apply hA
    simpa only [hXA] using hX.1
  have hSAeq : SA = commutingGraphEdgeWing c A B := by
    apply Set.eq_of_subset_of_ncard_le hSAsub
    rw [hSAcard, firstCase_edgeWing_ncard_three hmin c hfirst d hAB]
  have hSBeq : SB = commutingGraphEdgeWing c B A := by
    apply Set.eq_of_subset_of_ncard_le hSBsub
    rw [hSBcard, firstCase_edgeWing_ncard_three hmin c hfirst d hAB.symm]
  have hWingA_sub : commutingGraphEdgeWing c A B ⊆ S := by
    intro X hX
    have hX' : X ∈ SA := hSAeq.symm ▸ hX
    exact hX'.1
  have hWingB_sub : commutingGraphEdgeWing c B A ⊆ S := by
    intro X hX
    have hX' : X ∈ SB := hSBeq.symm ▸ hX
    exact hX'.1
  have hsubset : S ⊆ commutingGraphEdgeStar c A B := by
    intro X hXS
    by_cases hXL : X ∈ commutingGraphEdgeWing c A B
    · exact Or.inl (Or.inl hXL)
    by_cases hXR : X ∈ commutingGraphEdgeWing c B A
    · exact Or.inl (Or.inr hXR)
    right
    have hXA : X ≠ A := by
      intro hXA
      apply hA
      simpa only [hXA] using hXS
    have hXB : X ≠ B := by
      intro hXB
      apply hB
      simpa only [hXB] using hXS
    constructor
    · refine ⟨hXA.symm, ?_, ?_⟩
      · intro hAX
        exact hXL ⟨hAX, hXB⟩
      · rintro ⟨Q, hAQ, hQX⟩
        by_cases hQB : Q = B
        · subst Q
          exact hXR ⟨hQX, hXA⟩
        · have hQWing : Q ∈ commutingGraphEdgeWing c A B := ⟨hAQ, hQB⟩
          have hQS : Q ∈ S := hWingA_sub hQWing
          exact (hS hQS hXS hQX.ne) hQX
    · refine ⟨hXB.symm, ?_, ?_⟩
      · intro hBX
        exact hXR ⟨hBX, hXA⟩
      · rintro ⟨Q, hBQ, hQX⟩
        by_cases hQA : Q = A
        · subst Q
          exact hXL ⟨hQX, hXB⟩
        · have hQWing : Q ∈ commutingGraphEdgeWing c B A := ⟨hBQ, hQA⟩
          have hQS : Q ∈ S := hWingB_sub hQWing
          exact (hS hQS hXS hQX.ne) hQX
  apply Set.eq_of_subset_of_ncard_le hsubset
  rw [hcard, firstCase_edgeStar_ncard_fifteen hmin c hfirst d hAB]

end

end CFSG.GorensteinWalter

