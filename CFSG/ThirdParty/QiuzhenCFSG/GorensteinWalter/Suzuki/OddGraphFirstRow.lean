module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphIntersection
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The first row of the Suzuki odd-graph intersection array

The root, its four neighbours, the fibre-four layer, and the fibre-two layer
exhaust the 35 vertices.  Combining this partition with the incidence
exclusion from `OddGraphIntersection` shows that every root neighbour is
adjacent to the root and to exactly three fibre-four vertices.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The canonical coset-to-line equivalence sends the base coset to `U`. -/
public theorem cosetLineEquiv_base
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c) :
    cosetLineEquiv hmin c hfirst (cosetInvolution_base c.Hhat) =
      UConjugates.base c := by
  unfold cosetInvolution_base
  simp only [inv_one]
  rw [cosetLineEquiv_mk]
  simp

/-- The four rooted pieces exhaust the 35 vertices. -/
public theorem firstCase_root_partition
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c) (V : UConjugates c) :
    V = UConjugates.base c ∨ V ∈ lineNeighbors c ∨
      V ∈ firstCaseRootLayerTwo hmin c hfirst ∨
        V ∈ firstCaseRootLayerFour hmin c hfirst := by
  classical
  let e := cosetLineEquiv hmin c hfirst
  let R : Set (UConjugates c) := {UConjugates.base c}
  let N : Set (UConjugates c) := lineNeighbors c
  let T : Set (UConjugates c) := firstCaseRootLayerTwo hmin c hfirst
  let F : Set (UConjugates c) := firstCaseRootLayerFour hmin c hfirst
  have hesymbase : e.symm (UConjugates.base c) = cosetInvolution_base c.Hhat := by
    apply e.injective
    rw [e.apply_symm_apply, cosetLineEquiv_base hmin c hfirst]
  have hRN : Disjoint R N := by
    rw [Set.disjoint_left]
    intro W hWR hWN
    have hWbase : W = UConjugates.base c := by simpa [R] using hWR
    have hWN' : lineNeighbor c W := by simpa [N] using hWN
    exact hWN'.1 hWbase
  have hRNT : Disjoint (R ∪ N) T := by
    rw [Set.disjoint_left]
    intro W hWRN hWT
    have hWT' : e.symm W ≠ cosetInvolution_base c.Hhat ∧
        Nat.card (cosetInvolution_fiber c.Hhat (e.symm W)) = 2 := hWT
    rcases hWRN with hWR | hWN
    · have hWbase : W = UConjugates.base c := by simpa [R] using hWR
      exact hWT'.1 (by rw [hWbase, hesymbase])
    · have hWN' : W ∈ lineNeighbors c := by simpa [N] using hWN
      have hzero := (firstCase_mem_lineNeighbors_iff_cosetLayer_zero
        hmin c hfirst d W).mp hWN'
      dsimp [e] at hWT'
      omega
  have hRNTF : Disjoint ((R ∪ N) ∪ T) F := by
    rw [Set.disjoint_left]
    intro W hWRNT hWF
    have hWF' : e.symm W ≠ cosetInvolution_base c.Hhat ∧
        Nat.card (cosetInvolution_fiber c.Hhat (e.symm W)) = 4 := hWF
    rcases hWRNT with hWRN | hWT
    · rcases hWRN with hWR | hWN
      · have hWbase : W = UConjugates.base c := by simpa [R] using hWR
        exact hWF'.1 (by rw [hWbase, hesymbase])
      · have hWN' : W ∈ lineNeighbors c := by simpa [N] using hWN
        have hzero := (firstCase_mem_lineNeighbors_iff_cosetLayer_zero
          hmin c hfirst d W).mp hWN'
        dsimp [e] at hWF'
        omega
    · have hWT' : Nat.card (cosetInvolution_fiber c.Hhat (e.symm W)) = 2 := hWT.2
      omega
  have hRcard : R.ncard = 1 := by simp [R]
  have hNcard : N.ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    change Nat.card (lineNeighborSet c) = 4
    exact neighbor_card_eq_four hmin c hfirst d
  have hTcard : T.ncard = 18 := by
    rw [← Nat.card_coe_set_eq]
    exact firstCaseRootLayerTwo_card hmin c hfirst d
  have hFcard : F.ncard = 12 := by
    rw [← Nat.card_coe_set_eq]
    exact firstCaseRootLayerFour_card hmin c hfirst d
  have hUnionCard : (((R ∪ N) ∪ T) ∪ F).ncard = 35 := by
    rw [Set.ncard_union_eq hRNTF, Set.ncard_union_eq hRNT,
      Set.ncard_union_eq hRN, hRcard, hNcard, hTcard, hFcard]
  have hAll : ((R ∪ N) ∪ T) ∪ F = Set.univ := by
    apply (Set.eq_univ_iff_ncard (((R ∪ N) ∪ T) ∪ F)).mpr
    rw [hUnionCard, firstCase_UConjugates_card hmin c hfirst d]
  have hmem : V ∈ ((R ∪ N) ∪ T) ∪ F := by rw [hAll]; trivial
  rcases hmem with hRNT | hF
  · rcases hRNT with hRN | hT
    · rcases hRN with hR | hN
      · exact Or.inl (by simpa [R] using hR)
      · exact Or.inr (Or.inl (by simpa [N] using hN))
    · exact Or.inr (Or.inr (Or.inl hT))
  · exact Or.inr (Or.inr (Or.inr hF))

/-- Every vertex adjacent to a root neighbour is either the root or lies in
the fibre-four layer. -/
public theorem firstCase_rootNeighbor_adjacent_mem_base_or_four
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c)
    (V : lineNeighborSet c) (W : UConjugates c)
    (hAdj : (commutingGraph c).Adj V.1 W) :
    W = UConjugates.base c ∨
      W ∈ firstCaseRootLayerFour hmin c hfirst := by
  rcases firstCase_root_partition hmin c hfirst d W with hbase | hN | hT | hF
  · exact Or.inl hbase
  · exfalso
    let WN : lineNeighborSet c := ⟨W, hN⟩
    have hAdj' := (commutingGraph_adj_iff c V.1 W).mp hAdj
    have hne : V.1 ≠ WN.1 := hAdj'.1
    exact neighbor_coclique hmin c hfirst d V WN hne hAdj'.2
  · exact False.elim
      (firstCase_rootNeighbor_not_adjacent_rootLayerTwo hmin c hfirst d V W hT hAdj)
  · exact Or.inr hF

/-- A root neighbour is adjacent to exactly three vertices of the fibre-four
layer; its fourth neighbour is the root itself. -/
public theorem firstCase_rootNeighbor_four_neighbors_card_three
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c) (V : lineNeighborSet c) :
    Nat.card {W : {W : UConjugates c //
      W ∈ firstCaseRootLayerFour hmin c hfirst} //
        (commutingGraph c).Adj V.1 W.1} = 3 := by
  classical
  let Full : Type (max 0 u) :=
    {W : UConjugates c // (commutingGraph c).Adj V.1 W}
  let Four : Type (max 0 u) := {W : {W : UConjugates c //
    W ∈ firstCaseRootLayerFour hmin c hfirst} //
      (commutingGraph c).Adj V.1 W.1}
  have hAdjBase : (commutingGraph c).Adj V.1 (UConjugates.base c) := by
    exact (commutingGraph_adj_iff c _ _).mpr
      ⟨V.2.1, lineCommutes.symm c V.2.2⟩
  let f : Full → Sum (Fin 1) Four := fun W =>
    if h : W.1 = UConjugates.base c then Sum.inl 0
    else Sum.inr ⟨⟨W.1, (firstCase_rootNeighbor_adjacent_mem_base_or_four
      hmin c hfirst d V W.1 W.2).resolve_left h⟩, W.2⟩
  let g : Sum (Fin 1) Four → Full
    | Sum.inl _ => ⟨UConjugates.base c, hAdjBase⟩
    | Sum.inr W => ⟨W.1.1, W.2⟩
  have hgf : Function.LeftInverse g f := by
    intro W
    dsimp [f]
    split_ifs with h
    · apply Subtype.ext
      exact h.symm
    · rfl
  have hfg : Function.RightInverse g f := by
    intro W
    rcases W with _ | W
    · simp [f, g]
      apply Subsingleton.elim
    · dsimp [f, g]
      have hne : W.1.1 ≠ UConjugates.base c := by
        intro h
        have hq := W.1.2
        rw [h] at hq
        have hbase := cosetLineEquiv_base hmin c hfirst
        have hesym : (cosetLineEquiv hmin c hfirst).symm
            (UConjugates.base c) = cosetInvolution_base c.Hhat := by
          apply (cosetLineEquiv hmin c hfirst).injective
          rw [(cosetLineEquiv hmin c hfirst).apply_symm_apply, hbase]
        exact hq.1 hesym
      simp [hne]
  let e : Full ≃ Sum (Fin 1) Four := Equiv.ofBijective f
    ⟨hgf.injective, hfg.surjective⟩
  have hfull : Nat.card Full = 4 :=
    firstCase_commutingGraph_degree_four hmin c hfirst d V.1
  have hsum : Nat.card Full = 1 + Nat.card Four := by
    calc
      Nat.card Full = Nat.card (Sum (Fin 1) Four) := Nat.card_congr e
      _ = Nat.card (Fin 1) + Nat.card Four := Nat.card_sum
      _ = 1 + Nat.card Four := by simp
  rw [hfull] at hsum
  change Nat.card Four = 3
  omega

end CFSG.GorensteinWalter
