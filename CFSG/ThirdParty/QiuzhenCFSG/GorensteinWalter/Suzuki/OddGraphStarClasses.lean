module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphEdgeStar
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The seven intrinsic edge-star classes

Oriented darts are classified by equality of their intrinsic fifteen-point
edge stars.  A class consists exactly of the darts whose two endpoints lie in
the twenty-point complement of that star.  Every complement vertex has one
complement neighbour, so each class contains twenty darts.  Since the graph
has 140 darts in total, there are exactly seven classes.
-/

namespace CFSG.GorensteinWalter

universe u

noncomputable section

@[expose] public def commutingGraphDartStar
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (d : (commutingGraph c).Dart) :
    Set (UConjugates c) :=
  commutingGraphEdgeStar c d.fst d.snd

@[expose] public def CommutingGraphEdgeStarClass
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) : Type u :=
  {S : Set (UConjugates c) //
    ∃ d : (commutingGraph c).Dart, commutingGraphDartStar c d = S}

@[expose] public def commutingGraphDartStarClass
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (d : (commutingGraph c).Dart) :
    CommutingGraphEdgeStarClass c :=
  ⟨commutingGraphDartStar c d, d, rfl⟩

public noncomputable instance
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) : Finite (CommutingGraphEdgeStarClass c) := by
  classical
  let := Fintype.ofFinite (UConjugates c)
  apply Finite.of_surjective (commutingGraphDartStarClass c)
  rintro ⟨S, d, hd⟩
  exact ⟨d, Subtype.ext hd⟩

private def outsideNeighbors
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (S : Set (UConjugates c))
    (v : UConjugates c) : Set (UConjugates c) :=
  {w | (commutingGraph c).Adj v w ∧ w ∉ S}

private theorem outsideNeighbors_ncard_one
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c)
    (S : Set (UConjugates c))
    (hS : (commutingGraph c).IsIndepSet S)
    (hcard : S.ncard = 15)
    (v : UConjugates c) (hv : v ∉ S) :
    (outsideNeighbors c S v).ncard = 1 := by
  classical
  let := Fintype.ofFinite (UConjugates c)
  let N : Set (UConjugates c) := {w | (commutingGraph c).Adj v w}
  let I : Set (UConjugates c) :=
    {w | w ∈ S ∧ (commutingGraph c).Adj v w}
  have hpartition : N = I ∪ outsideNeighbors c S v := by
    ext w
    constructor
    · intro hvw
      by_cases hw : w ∈ S
      · exact Or.inl ⟨hw, hvw⟩
      · exact Or.inr ⟨hvw, hw⟩
    · rintro (hw | hw)
      · exact hw.2
      · exact hw.1
  have hdisjoint : Disjoint I (outsideNeighbors c S v) := by
    refine Set.disjoint_left.2 ?_
    intro w hwI hwO
    exact hwO.2 hwI.1
  have hN : N.ncard = 4 := by
    change Nat.card {w : UConjugates c // (commutingGraph c).Adj v w} = 4
    exact firstCase_commutingGraph_degree_four hmin c hfirst d v
  have hI : I.ncard = 3 := by
    change Nat.card {w : UConjugates c //
      w ∈ S ∧ (commutingGraph c).Adj v w} = 3
    exact firstCase_indepSet_card_fifteen_outside_neighbors
      hmin c hfirst d S hS hcard v hv
  rw [hpartition, Set.ncard_union_eq hdisjoint, hI] at hN
  omega

private def outsideDarts
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (S : Set (UConjugates c)) : Type u :=
  {e : (commutingGraph c).Dart // e.fst ∉ S ∧ e.snd ∉ S}

private theorem outsideDarts_card_twenty
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c)
    (S : Set (UConjugates c))
    (hS : (commutingGraph c).IsIndepSet S)
    (hcard : S.ncard = 15) :
    Nat.card (outsideDarts c S) = 20 := by
  classical
  let := Fintype.ofFinite (UConjugates c)
  let e : outsideDarts c S ≃
      Σ v : {v : UConjugates c // v ∉ S},
        {w : UConjugates c // w ∈ outsideNeighbors c S v.1} :=
    { toFun := fun x =>
        ⟨⟨x.1.fst, x.2.1⟩, ⟨x.1.snd, ⟨x.1.adj, x.2.2⟩⟩⟩
      invFun := fun x =>
        ⟨⟨(x.1.1, x.2.1), x.2.2.1⟩, ⟨x.1.2, x.2.2.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hbase : Nat.card {v : UConjugates c // v ∉ S} = 20 := by
    change Sᶜ.ncard = 20
    apply Set.ncard_compl_of_ncard_eq_add S
    rw [firstCase_UConjugates_card hmin c hfirst d, hcard]
  calc
    Nat.card (outsideDarts c S) =
        Nat.card (Σ v : {v : UConjugates c // v ∉ S},
          {w : UConjugates c // w ∈ outsideNeighbors c S v.1}) :=
      Nat.card_congr e
    _ = ∑ v : {v : UConjugates c // v ∉ S},
        Nat.card {w : UConjugates c // w ∈ outsideNeighbors c S v.1} := by
      rw [Nat.card_sigma]
    _ = ∑ _v : {v : UConjugates c // v ∉ S}, 1 := by
      apply Finset.sum_congr rfl
      intro v _
      change (outsideNeighbors c S v.1).ncard = 1
      exact outsideNeighbors_ncard_one hmin c hfirst d S hS hcard v.1 v.2
    _ = Nat.card {v : UConjugates c // v ∉ S} := by simp
    _ = 20 := hbase

public theorem firstCase_edgeStarClass_fiber_card_twenty
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c)
    (S : CommutingGraphEdgeStarClass c) :
    Nat.card {e : (commutingGraph c).Dart // commutingGraphDartStarClass c e = S} = 20 := by
  classical
  obtain ⟨d0, hd0⟩ := S.2
  have hSindep : (commutingGraph c).IsIndepSet S.1 := by
    rw [← hd0]
    exact firstCase_edgeStar_isIndepSet hmin c hfirst d d0.adj
  have hScard : S.1.ncard = 15 := by
    rw [← hd0]
    exact firstCase_edgeStar_ncard_fifteen hmin c hfirst d d0.adj
  let e :
      {x : (commutingGraph c).Dart // commutingGraphDartStarClass c x = S} ≃
        outsideDarts c S.1 :=
    { toFun := fun x => ⟨x.1, by
        have hstar : commutingGraphDartStar c x.1 = S.1 := congrArg Subtype.val x.2
        change commutingGraphEdgeStar c x.1.fst x.1.snd = S.1 at hstar
        have hend := commutingGraphEdgeStar_endpoints_not_mem
          c x.1.fst x.1.snd
        constructor
        · intro hx
          apply hend.1
          rw [hstar]
          exact hx
        · intro hx
          apply hend.2
          rw [hstar]
          exact hx⟩
      invFun := fun x => ⟨x.1, by
        apply Subtype.ext
        change commutingGraphDartStar c x.1 = S.1
        exact (firstCase_edgeStar_unique hmin c hfirst d x.1.adj
          S.1 hSindep hScard x.2.1 x.2.2).symm⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl }
  calc
    Nat.card {x : (commutingGraph c).Dart // commutingGraphDartStarClass c x = S} =
        Nat.card (outsideDarts c S.1) := Nat.card_congr e
    _ = 20 := outsideDarts_card_twenty
      hmin c hfirst d S.1 hSindep hScard

private theorem commutingGraph_degree_eq_four
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c)
    [Fintype (UConjugates c)]
    [DecidableRel (commutingGraph c).Adj]
    (v : UConjugates c) :
    (commutingGraph c).degree v = 4 := by
  rw [← (commutingGraph c).card_neighborSet_eq_degree]
  rw [← Nat.card_eq_fintype_card]
  exact firstCase_commutingGraph_degree_four hmin c hfirst d v

private theorem commutingGraph_dart_card_oneForty
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c) :
    Nat.card (commutingGraph c).Dart = 140 := by
  classical
  let := Fintype.ofFinite (UConjugates c)
  have hV : Fintype.card (UConjugates c) = 35 := by
    rw [← Nat.card_eq_fintype_card]
    exact firstCase_UConjugates_card hmin c hfirst d
  rw [Nat.card_eq_fintype_card, (commutingGraph c).dart_card_eq_sum_degrees]
  simp_rw [commutingGraph_degree_eq_four hmin c hfirst d]
  simp [hV]

public theorem firstCase_edgeStarClass_card_seven
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c) :
    Nat.card (CommutingGraphEdgeStarClass c) = 7 := by
  classical
  let := Fintype.ofFinite (UConjugates c)
  let := Fintype.ofFinite (CommutingGraphEdgeStarClass c)
  let f := commutingGraphDartStarClass c
  have hdecomp :
      Nat.card (commutingGraph c).Dart =
        ∑ S : CommutingGraphEdgeStarClass c,
          Nat.card {e : (commutingGraph c).Dart // f e = S} := by
    calc
      Nat.card (commutingGraph c).Dart =
          Nat.card (Σ S : CommutingGraphEdgeStarClass c,
            {e : (commutingGraph c).Dart // f e = S}) :=
        (Nat.card_congr (Equiv.sigmaFiberEquiv f)).symm
      _ = ∑ S : CommutingGraphEdgeStarClass c,
          Nat.card {e : (commutingGraph c).Dart // f e = S} := by
        rw [Nat.card_sigma]
  have hEq : 140 = Nat.card (CommutingGraphEdgeStarClass c) * 20 := by
    calc
      140 = Nat.card (commutingGraph c).Dart :=
        (commutingGraph_dart_card_oneForty hmin c hfirst d).symm
      _ = ∑ S : CommutingGraphEdgeStarClass c,
          Nat.card {e : (commutingGraph c).Dart // f e = S} := hdecomp
      _ = ∑ _S : CommutingGraphEdgeStarClass c, 20 := by
        apply Finset.sum_congr rfl
        intro S _
        exact firstCase_edgeStarClass_fiber_card_twenty hmin c hfirst d S
      _ = Nat.card (CommutingGraphEdgeStarClass c) * 20 := by
        rw [Nat.card_eq_fintype_card]
        simp
  omega

/-- Every edge-star class is represented by a commuting-graph dart. -/
public theorem commutingGraphDartStarClass_surjective
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) :
    Function.Surjective (commutingGraphDartStarClass c) := by
  rintro ⟨S, d, hd⟩
  exact ⟨d, Subtype.ext hd⟩

end

end CFSG.GorensteinWalter
