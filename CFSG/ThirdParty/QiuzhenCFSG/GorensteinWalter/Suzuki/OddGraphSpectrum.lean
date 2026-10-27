module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphDistance
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# A spectral coclique bound for the Suzuki commuting graph

The transported distance array gives a polynomial identity for the adjacency
matrix.  A sum-of-squares certificate then bounds independent sets by fifteen.
Equality forces the complement to be one-regular across the cut: every vertex
outside a fifteen-point independent set has exactly three neighbours in it.
-/

open Matrix Finset
open scoped Polynomial

namespace CFSG.GorensteinWalter

universe u

noncomputable section

private noncomputable def spectrumAdjMatrix
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) :
    Matrix (UConjugates c) (UConjugates c) ℝ := by
  classical
  exact (commutingGraph c).adjMatrix ℝ

private theorem spectrumAdjMatrix_apply_of
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (A B : UConjugates c)
    (h : (commutingGraph c).Adj A B) :
    spectrumAdjMatrix c A B = 1 := by
  classical
  change (if (commutingGraph c).Adj A B then (1 : ℝ) else 0) = 1
  rw [if_pos h]

private theorem spectrumAdjMatrix_apply_of_not
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (A B : UConjugates c)
    (h : ¬ (commutingGraph c).Adj A B) :
    spectrumAdjMatrix c A B = 0 := by
  classical
  change (if (commutingGraph c).Adj A B then (1 : ℝ) else 0) = 0
  rw [if_neg h]

private noncomputable def spectrumDistTwoMatrix
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) :
    Matrix (UConjugates c) (UConjugates c) ℝ := by
  classical
  exact fun A B => if commutingGraphDistTwo c A B then 1 else 0

private noncomputable def spectrumDistThreeMatrix
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) :
    Matrix (UConjugates c) (UConjugates c) ℝ := by
  classical
  exact fun A B => if commutingGraphDistThree c A B then 1 else 0

private theorem spectrumDistTwoMatrix_apply_of
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (A B : UConjugates c)
    (h : commutingGraphDistTwo c A B) :
    spectrumDistTwoMatrix c A B = 1 := by
  classical
  simp [spectrumDistTwoMatrix, h]

private theorem spectrumDistTwoMatrix_apply_of_not
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (A B : UConjugates c)
    (h : ¬ commutingGraphDistTwo c A B) :
    spectrumDistTwoMatrix c A B = 0 := by
  classical
  simp [spectrumDistTwoMatrix, h]

private theorem spectrumDistThreeMatrix_apply_of
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (A B : UConjugates c)
    (h : commutingGraphDistThree c A B) :
    spectrumDistThreeMatrix c A B = 1 := by
  classical
  simp [spectrumDistThreeMatrix, h]

private theorem spectrumDistThreeMatrix_apply_of_not
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (A B : UConjugates c)
    (h : ¬ commutingGraphDistThree c A B) :
    spectrumDistThreeMatrix c A B = 0 := by
  classical
  simp [spectrumDistThreeMatrix, h]

private def spectrumAllOnes
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) :
    Matrix (UConjugates c) (UConjugates c) ℝ :=
  fun _ _ => 1

private noncomputable def spectrumScalarMatrix
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) [Fintype (UConjugates c)] (r : ℝ) :
    Matrix (UConjugates c) (UConjugates c) ℝ := by
  classical
  exact Matrix.scalar (UConjugates c) r

private theorem spectrumScalarMatrix_apply_self
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) [Fintype (UConjugates c)]
    (r : ℝ) (i : UConjugates c) :
    spectrumScalarMatrix c r i i = r := by
  classical
  simp [spectrumScalarMatrix]

private theorem spectrumScalarMatrix_apply_of_ne
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) [Fintype (UConjugates c)]
    (r : ℝ) {i j : UConjugates c} (hij : i ≠ j) :
    spectrumScalarMatrix c r i j = 0 := by
  classical
  simp [spectrumScalarMatrix, hij]

private theorem adjMatrix_mul_adjMatrix_apply_eq_commonNeighbor_card
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) [Fintype (UConjugates c)]
    (i j : UConjugates c) :
    (spectrumAdjMatrix c * spectrumAdjMatrix c) i j =
      Nat.card {k : UConjugates c //
        (commutingGraph c).Adj i k ∧ (commutingGraph c).Adj k j} := by
  classical
  let e :
      {k // k ∈ ((commutingGraph c).neighborFinset i).filter
        (fun k => (commutingGraph c).Adj k j)} ≃
        {k : UConjugates c //
          (commutingGraph c).Adj i k ∧ (commutingGraph c).Adj k j} :=
    { toFun := fun k => ⟨k.1, by
        rcases Finset.mem_filter.mp k.2 with ⟨hik, hkj⟩
        exact ⟨(SimpleGraph.mem_neighborFinset _ _ _).mp hik, hkj⟩⟩
      invFun := fun k => ⟨k.1, Finset.mem_filter.mpr
        ⟨(SimpleGraph.mem_neighborFinset _ _ _).mpr k.2.1, k.2.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simp only [spectrumAdjMatrix, SimpleGraph.adjMatrix_mul_apply]
  calc
    (∑ k ∈ (commutingGraph c).neighborFinset i,
        if (commutingGraph c).Adj k j then (1 : ℝ) else 0) =
        (((commutingGraph c).neighborFinset i).filter
          (fun k => (commutingGraph c).Adj k j)).card := by simp
    _ = Fintype.card {k : UConjugates c //
        (commutingGraph c).Adj i k ∧ (commutingGraph c).Adj k j} := by
      exact_mod_cast (Fintype.card_coe _).symm.trans (Fintype.card_congr e)
    _ = Nat.card {k : UConjugates c //
        (commutingGraph c).Adj i k ∧ (commutingGraph c).Adj k j} := by
      rw [Nat.card_eq_fintype_card]

private def commonNeighborSelfEquiv
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (i : UConjugates c) :
    {k : UConjugates c //
      (commutingGraph c).Adj i k ∧ (commutingGraph c).Adj k i} ≃
      {k : UConjugates c // (commutingGraph c).Adj i k} where
  toFun k := ⟨k.1, k.2.1⟩
  invFun k := ⟨k.1, ⟨k.2, k.2.symm⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem commonNeighbor_card_eq_one
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c)
    {i j : UConjugates c}
    (hij : i ≠ j)
    (hcommon : commutingGraphHasCommonNeighbor c i j) :
    Nat.card {k : UConjugates c //
      (commutingGraph c).Adj i k ∧ (commutingGraph c).Adj k j} = 1 := by
  rcases hcommon with ⟨k, hik, hkj⟩
  apply Nat.card_eq_one_iff_unique.mpr
  refine ⟨?_, ⟨⟨k, hik, hkj⟩⟩⟩
  constructor
  intro x y
  apply Subtype.ext
  exact firstCase_commutingGraph_commonNeighbor_unique hmin c hfirst d
    hij x.2.1 x.2.2 y.2.1 y.2.2

private theorem commonNeighbor_card_eq_zero
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    {i j : UConjugates c}
    (hcommon : ¬ commutingGraphHasCommonNeighbor c i j) :
    Nat.card {k : UConjugates c //
      (commutingGraph c).Adj i k ∧ (commutingGraph c).Adj k j} = 0 := by
  rw [Nat.card_eq_zero]
  left
  constructor
  intro k
  exact hcommon ⟨k.1, k.2.1, k.2.2⟩

private theorem spectrum_adj_sq
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c)
    [Fintype (UConjugates c)] :
    spectrumAdjMatrix c * spectrumAdjMatrix c =
      spectrumScalarMatrix c 4 +
        spectrumDistTwoMatrix c := by
  classical
  ext i j
  rw [adjMatrix_mul_adjMatrix_apply_eq_commonNeighbor_card]
  by_cases hij : i = j
  · subst j
    rw [Nat.card_congr (commonNeighborSelfEquiv c i),
      firstCase_commutingGraph_degree_four hmin c hfirst d i]
    have hnotDist : ¬ commutingGraphDistTwo c i i := fun h => h.1 rfl
    rw [Matrix.add_apply, spectrumScalarMatrix_apply_self,
      spectrumDistTwoMatrix_apply_of_not c i i hnotDist]
    norm_num
  · by_cases hadj : (commutingGraph c).Adj i j
    · have hnoCommon : ¬ commutingGraphHasCommonNeighbor c i j := by
        rintro ⟨k, hik, hkj⟩
        exact firstCase_commutingGraph_triangle_free
          hmin c hfirst d hik hadj hkj
      rw [commonNeighbor_card_eq_zero c hnoCommon]
      have hnotDist : ¬ commutingGraphDistTwo c i j := fun h => h.2.1 hadj
      rw [Matrix.add_apply, spectrumScalarMatrix_apply_of_ne c 4 hij,
        spectrumDistTwoMatrix_apply_of_not c i j hnotDist]
      norm_num
    · by_cases hcommon : commutingGraphHasCommonNeighbor c i j
      · rw [commonNeighbor_card_eq_one hmin c hfirst d hij hcommon]
        rw [Matrix.add_apply, spectrumScalarMatrix_apply_of_ne c 4 hij,
          spectrumDistTwoMatrix_apply_of c i j ⟨hij, hadj, hcommon⟩]
        norm_num
      · rw [commonNeighbor_card_eq_zero c hcommon]
        have hnotDist : ¬ commutingGraphDistTwo c i j := fun h => hcommon h.2.2
        rw [Matrix.add_apply, spectrumScalarMatrix_apply_of_ne c 4 hij,
          spectrumDistTwoMatrix_apply_of_not c i j hnotDist]
        norm_num

private theorem adjMatrix_mul_distTwo_apply_eq_card
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) [Fintype (UConjugates c)]
    (i j : UConjugates c) :
    (spectrumAdjMatrix c * spectrumDistTwoMatrix c) i j =
      Nat.card {k : UConjugates c //
        (commutingGraph c).Adj i k ∧ commutingGraphDistTwo c k j} := by
  classical
  let e :
      {k // k ∈ ((commutingGraph c).neighborFinset i).filter
        (fun k => commutingGraphDistTwo c k j)} ≃
        {k : UConjugates c //
          (commutingGraph c).Adj i k ∧ commutingGraphDistTwo c k j} :=
    { toFun := fun k => ⟨k.1, by
        rcases Finset.mem_filter.mp k.2 with ⟨hik, hkj⟩
        exact ⟨(SimpleGraph.mem_neighborFinset _ _ _).mp hik, hkj⟩⟩
      invFun := fun k => ⟨k.1, Finset.mem_filter.mpr
        ⟨(SimpleGraph.mem_neighborFinset _ _ _).mpr k.2.1, k.2.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simp only [spectrumAdjMatrix, SimpleGraph.adjMatrix_mul_apply]
  calc
    (∑ k ∈ (commutingGraph c).neighborFinset i,
        spectrumDistTwoMatrix c k j) =
        ∑ k ∈ (commutingGraph c).neighborFinset i,
          if commutingGraphDistTwo c k j then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases h : commutingGraphDistTwo c k j
      · rw [if_pos h, spectrumDistTwoMatrix_apply_of c k j h]
      · rw [if_neg h, spectrumDistTwoMatrix_apply_of_not c k j h]
    _ = (((commutingGraph c).neighborFinset i).filter
          (fun k => commutingGraphDistTwo c k j)).card := by simp
    _ = Fintype.card {k : UConjugates c //
        (commutingGraph c).Adj i k ∧ commutingGraphDistTwo c k j} := by
      exact_mod_cast (Fintype.card_coe _).symm.trans (Fintype.card_congr e)
    _ = Nat.card {k : UConjugates c //
        (commutingGraph c).Adj i k ∧ commutingGraphDistTwo c k j} := by
      rw [Nat.card_eq_fintype_card]

private theorem adjMatrix_mul_distThree_apply_eq_card
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) [Fintype (UConjugates c)]
    (i j : UConjugates c) :
    (spectrumAdjMatrix c * spectrumDistThreeMatrix c) i j =
      Nat.card {k : UConjugates c //
        (commutingGraph c).Adj i k ∧ commutingGraphDistThree c k j} := by
  classical
  let e :
      {k // k ∈ ((commutingGraph c).neighborFinset i).filter
        (fun k => commutingGraphDistThree c k j)} ≃
        {k : UConjugates c //
          (commutingGraph c).Adj i k ∧ commutingGraphDistThree c k j} :=
    { toFun := fun k => ⟨k.1, by
        rcases Finset.mem_filter.mp k.2 with ⟨hik, hkj⟩
        exact ⟨(SimpleGraph.mem_neighborFinset _ _ _).mp hik, hkj⟩⟩
      invFun := fun k => ⟨k.1, Finset.mem_filter.mpr
        ⟨(SimpleGraph.mem_neighborFinset _ _ _).mpr k.2.1, k.2.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simp only [spectrumAdjMatrix, SimpleGraph.adjMatrix_mul_apply]
  calc
    (∑ k ∈ (commutingGraph c).neighborFinset i,
        spectrumDistThreeMatrix c k j) =
        ∑ k ∈ (commutingGraph c).neighborFinset i,
          if commutingGraphDistThree c k j then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases h : commutingGraphDistThree c k j
      · rw [if_pos h, spectrumDistThreeMatrix_apply_of c k j h]
      · rw [if_neg h, spectrumDistThreeMatrix_apply_of_not c k j h]
    _ = (((commutingGraph c).neighborFinset i).filter
          (fun k => commutingGraphDistThree c k j)).card := by simp
    _ = Fintype.card {k : UConjugates c //
        (commutingGraph c).Adj i k ∧ commutingGraphDistThree c k j} := by
      exact_mod_cast (Fintype.card_coe _).symm.trans (Fintype.card_congr e)
    _ = Nat.card {k : UConjugates c //
        (commutingGraph c).Adj i k ∧ commutingGraphDistThree c k j} := by
      rw [Nat.card_eq_fintype_card]

private def distTwoIncidenceEquiv
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (i j : UConjugates c) :
    {k : UConjugates c //
      (commutingGraph c).Adj i k ∧ commutingGraphDistTwo c k j} ≃
      {k : {k : UConjugates c // commutingGraphDistTwo c j k} //
        (commutingGraph c).Adj i k.1} where
  toFun k := ⟨⟨k.1, (commutingGraphDistTwo_comm c k.1 j).mp k.2.2⟩, k.2.1⟩
  invFun k := ⟨k.1.1, k.2, (commutingGraphDistTwo_comm c k.1.1 j).mpr k.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def distThreeIncidenceEquiv
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (i j : UConjugates c) :
    {k : UConjugates c //
      (commutingGraph c).Adj i k ∧ commutingGraphDistThree c k j} ≃
      {k : {k : UConjugates c // commutingGraphDistThree c j k} //
        (commutingGraph c).Adj i k.1} where
  toFun k := ⟨⟨k.1, (commutingGraphDistThree_comm c k.1 j).mp k.2.2⟩, k.2.1⟩
  invFun k := ⟨k.1.1, k.2, (commutingGraphDistThree_comm c k.1.1 j).mpr k.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem adjacent_distTwo_incidence_card_three
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c)
    {i j : UConjugates c} (hij : (commutingGraph c).Adj i j) :
    Nat.card {k : UConjugates c //
      (commutingGraph c).Adj i k ∧ commutingGraphDistTwo c k j} = 3 := by
  let T : Set (UConjugates c) :=
    {k | (commutingGraph c).Adj i k ∧ commutingGraphDistTwo c k j}
  let N : Set (UConjugates c) := {k | (commutingGraph c).Adj i k}
  have hTN : T = N \ {j} := by
    ext k
    constructor
    · rintro ⟨hik, hdist⟩
      exact ⟨hik, by simpa using hdist.1⟩
    · rintro ⟨hik, hkj⟩
      have hkne : k ≠ j := by simpa using hkj
      have hnotAdj : ¬ (commutingGraph c).Adj k j :=
        firstCase_commutingGraph_triangle_free hmin c hfirst d hik hij
      exact ⟨hik, hkne, hnotAdj, ⟨i, hik.symm, hij⟩⟩
  calc
    Nat.card {k : UConjugates c //
        (commutingGraph c).Adj i k ∧ commutingGraphDistTwo c k j} =
        T.ncard := by
      exact Nat.card_coe_set_eq T
    _ = (N \ {j}).ncard := by rw [hTN]
    _ = N.ncard - 1 := Set.ncard_sdiff_singleton_of_mem hij
    _ = Nat.card N - 1 := by rw [Nat.card_coe_set_eq N]
    _ = Nat.card {k : UConjugates c //
        (commutingGraph c).Adj i k} - 1 := by rfl
    _ = 3 := by
      rw [firstCase_commutingGraph_degree_four hmin c hfirst d i]

private theorem spectrum_adj_mul_distTwo
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c)
    [Fintype (UConjugates c)] :
    spectrumAdjMatrix c * spectrumDistTwoMatrix c =
      (3 : ℝ) • spectrumAdjMatrix c +
        (2 : ℝ) • spectrumDistThreeMatrix c := by
  classical
  ext i j
  rw [adjMatrix_mul_distTwo_apply_eq_card]
  by_cases hij : i = j
  · subst j
    have hcard : Nat.card {k : UConjugates c //
        (commutingGraph c).Adj i k ∧ commutingGraphDistTwo c k i} = 0 := by
      rw [Nat.card_eq_zero]
      left
      constructor
      intro k
      exact k.2.2.2.1 k.2.1.symm
    rw [hcard, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply,
      spectrumAdjMatrix_apply_of_not c i i (commutingGraph c).irrefl]
    have hnotDist : ¬ commutingGraphDistThree c i i := fun h => h.1 rfl
    rw [spectrumDistThreeMatrix_apply_of_not c i i hnotDist]
    norm_num
  · by_cases hadj : (commutingGraph c).Adj i j
    · rw [adjacent_distTwo_incidence_card_three hmin c hfirst d hadj,
        Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply,
        spectrumAdjMatrix_apply_of c i j hadj]
      have hnotDist : ¬ commutingGraphDistThree c i j := fun h => h.2.1 hadj
      rw [spectrumDistThreeMatrix_apply_of_not c i j hnotDist]
      norm_num
    · by_cases hcommon : commutingGraphHasCommonNeighbor c i j
      · let hdist : commutingGraphDistTwo c i j := ⟨hij, hadj, hcommon⟩
        have hcard : Nat.card {k : UConjugates c //
            (commutingGraph c).Adj i k ∧ commutingGraphDistTwo c k j} = 0 := by
          rw [Nat.card_congr (distTwoIncidenceEquiv c i j)]
          exact firstCase_distTwo_internal_neighbors_card_zero
            hmin c hfirst d j i ((commutingGraphDistTwo_comm c i j).mp hdist)
        rw [hcard, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply,
          spectrumAdjMatrix_apply_of_not c i j hadj]
        have hnotDistThree : ¬ commutingGraphDistThree c i j :=
          fun h => h.2.2 hcommon
        rw [spectrumDistThreeMatrix_apply_of_not c i j hnotDistThree]
        norm_num
      · let hdist : commutingGraphDistThree c i j := ⟨hij, hadj, hcommon⟩
        have hcard : Nat.card {k : UConjugates c //
            (commutingGraph c).Adj i k ∧ commutingGraphDistTwo c k j} = 2 := by
          rw [Nat.card_congr (distTwoIncidenceEquiv c i j)]
          exact firstCase_distThree_distTwo_neighbors_card_two
            hmin c hfirst d j i ((commutingGraphDistThree_comm c i j).mp hdist)
        rw [hcard, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply,
          spectrumAdjMatrix_apply_of_not c i j hadj,
          spectrumDistThreeMatrix_apply_of c i j hdist]
        norm_num

private theorem spectrum_adj_mul_distThree
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c)
    [Fintype (UConjugates c)] :
    spectrumAdjMatrix c * spectrumDistThreeMatrix c =
      (3 : ℝ) • spectrumDistTwoMatrix c +
        (2 : ℝ) • spectrumDistThreeMatrix c := by
  classical
  ext i j
  rw [adjMatrix_mul_distThree_apply_eq_card]
  by_cases hij : i = j
  · subst j
    have hcard : Nat.card {k : UConjugates c //
        (commutingGraph c).Adj i k ∧ commutingGraphDistThree c k i} = 0 := by
      rw [Nat.card_eq_zero]
      left
      constructor
      intro k
      exact k.2.2.2.1 k.2.1.symm
    rw [hcard, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply]
    have hnotTwo : ¬ commutingGraphDistTwo c i i := fun h => h.1 rfl
    have hnotThree : ¬ commutingGraphDistThree c i i := fun h => h.1 rfl
    rw [spectrumDistTwoMatrix_apply_of_not c i i hnotTwo,
      spectrumDistThreeMatrix_apply_of_not c i i hnotThree]
    norm_num
  · by_cases hadj : (commutingGraph c).Adj i j
    · have hcard : Nat.card {k : UConjugates c //
          (commutingGraph c).Adj i k ∧ commutingGraphDistThree c k j} = 0 := by
        rw [Nat.card_eq_zero]
        left
        constructor
        intro k
        exact k.2.2.2.2 ⟨i, k.2.1.symm, hadj⟩
      rw [hcard, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply]
      have hnotTwo : ¬ commutingGraphDistTwo c i j := fun h => h.2.1 hadj
      have hnotThree : ¬ commutingGraphDistThree c i j := fun h => h.2.1 hadj
      rw [spectrumDistTwoMatrix_apply_of_not c i j hnotTwo,
        spectrumDistThreeMatrix_apply_of_not c i j hnotThree]
      norm_num
    · by_cases hcommon : commutingGraphHasCommonNeighbor c i j
      · let hdist : commutingGraphDistTwo c i j := ⟨hij, hadj, hcommon⟩
        have hcard : Nat.card {k : UConjugates c //
            (commutingGraph c).Adj i k ∧ commutingGraphDistThree c k j} = 3 := by
          rw [Nat.card_congr (distThreeIncidenceEquiv c i j)]
          exact firstCase_distTwo_distThree_neighbors_card_three
            hmin c hfirst d j i ((commutingGraphDistTwo_comm c i j).mp hdist)
        rw [hcard, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply,
          spectrumDistTwoMatrix_apply_of c i j hdist]
        have hnotThree : ¬ commutingGraphDistThree c i j :=
          fun h => h.2.2 hcommon
        rw [spectrumDistThreeMatrix_apply_of_not c i j hnotThree]
        norm_num
      · let hdist : commutingGraphDistThree c i j := ⟨hij, hadj, hcommon⟩
        have hcard : Nat.card {k : UConjugates c //
            (commutingGraph c).Adj i k ∧ commutingGraphDistThree c k j} = 2 := by
          rw [Nat.card_congr (distThreeIncidenceEquiv c i j)]
          exact firstCase_distThree_internal_neighbors_card_two
            hmin c hfirst d j i ((commutingGraphDistThree_comm c i j).mp hdist)
        rw [hcard, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply]
        have hnotTwo : ¬ commutingGraphDistTwo c i j :=
          fun h => hcommon h.2.2
        rw [spectrumDistTwoMatrix_apply_of_not c i j hnotTwo,
          spectrumDistThreeMatrix_apply_of c i j hdist]
        norm_num

private theorem spectrum_partition
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) [Fintype (UConjugates c)] :
    spectrumScalarMatrix c 1 + spectrumAdjMatrix c +
        spectrumDistTwoMatrix c + spectrumDistThreeMatrix c =
      spectrumAllOnes c := by
  classical
  ext i j
  simp only [Matrix.add_apply]
  by_cases hij : i = j
  · subst j
    rw [spectrumScalarMatrix_apply_self,
      spectrumAdjMatrix_apply_of_not c i i (commutingGraph c).irrefl]
    have hnotTwo : ¬ commutingGraphDistTwo c i i := fun h => h.1 rfl
    have hnotThree : ¬ commutingGraphDistThree c i i := fun h => h.1 rfl
    rw [spectrumDistTwoMatrix_apply_of_not c i i hnotTwo,
      spectrumDistThreeMatrix_apply_of_not c i i hnotThree]
    norm_num [spectrumAllOnes]
  · rw [spectrumScalarMatrix_apply_of_ne c 1 hij]
    by_cases hadj : (commutingGraph c).Adj i j
    · rw [spectrumAdjMatrix_apply_of c i j hadj]
      have hnotTwo : ¬ commutingGraphDistTwo c i j := fun h => h.2.1 hadj
      have hnotThree : ¬ commutingGraphDistThree c i j := fun h => h.2.1 hadj
      rw [spectrumDistTwoMatrix_apply_of_not c i j hnotTwo,
        spectrumDistThreeMatrix_apply_of_not c i j hnotThree]
      norm_num [spectrumAllOnes]
    · rw [spectrumAdjMatrix_apply_of_not c i j hadj]
      by_cases hcommon : commutingGraphHasCommonNeighbor c i j
      · let htwo : commutingGraphDistTwo c i j := ⟨hij, hadj, hcommon⟩
        have hnotThree : ¬ commutingGraphDistThree c i j :=
          fun h => h.2.2 hcommon
        rw [spectrumDistTwoMatrix_apply_of c i j htwo,
          spectrumDistThreeMatrix_apply_of_not c i j hnotThree]
        norm_num [spectrumAllOnes]
      · let hthree : commutingGraphDistThree c i j := ⟨hij, hadj, hcommon⟩
        have hnotTwo : ¬ commutingGraphDistTwo c i j :=
          fun h => hcommon h.2.2
        rw [spectrumDistTwoMatrix_apply_of_not c i j hnotTwo,
          spectrumDistThreeMatrix_apply_of c i j hthree]
        norm_num [spectrumAllOnes]

private theorem spectrumScalarMatrix_eq_matrixScalar
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) [Fintype (UConjugates c)]
    [DecidableEq (UConjugates c)] (r : ℝ) :
    spectrumScalarMatrix c r = Matrix.scalar (UConjugates c) r := by
  ext i j
  by_cases hij : i = j
  · subst j
    rw [spectrumScalarMatrix_apply_self]
    simp
  · rw [spectrumScalarMatrix_apply_of_ne c r hij]
    simp [Matrix.scalar_apply, hij]

private theorem spectrumScalarMatrix_mul
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) [Fintype (UConjugates c)]
    [DecidableEq (UConjugates c)] (r : ℝ)
    (M : Matrix (UConjugates c) (UConjugates c) ℝ) :
    spectrumScalarMatrix c r * M = r • M := by
  rw [spectrumScalarMatrix_eq_matrixScalar, Matrix.scalar_apply,
    ← Matrix.smul_eq_diagonal_mul]

private theorem mul_spectrumScalarMatrix
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) [Fintype (UConjugates c)]
    [DecidableEq (UConjugates c)]
    (M : Matrix (UConjugates c) (UConjugates c) ℝ) (r : ℝ) :
    M * spectrumScalarMatrix c r = r • M := by
  rw [spectrumScalarMatrix_eq_matrixScalar, Matrix.scalar_apply]
  ext i j
  simp [mul_comm]

private theorem smul_spectrumScalarMatrix
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) [Fintype (UConjugates c)]
    [DecidableEq (UConjugates c)] (r s : ℝ) :
    r • spectrumScalarMatrix c s = spectrumScalarMatrix c (r * s) := by
  rw [spectrumScalarMatrix_eq_matrixScalar,
    spectrumScalarMatrix_eq_matrixScalar]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.scalar_apply]
  · simp [Matrix.scalar_apply, hij]

private theorem spectrumScalarMatrix_eq_smul_one
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) [Fintype (UConjugates c)]
    [DecidableEq (UConjugates c)] (r : ℝ) :
    spectrumScalarMatrix c r = r • spectrumScalarMatrix c 1 := by
  rw [smul_spectrumScalarMatrix]
  simp

private theorem spectrumScalarMatrix_eq_algebraMap
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) [Fintype (UConjugates c)]
    [DecidableEq (UConjugates c)] (r : ℝ) :
    spectrumScalarMatrix c r =
      algebraMap ℝ (Matrix (UConjugates c) (UConjugates c) ℝ) r := by
  rw [spectrumScalarMatrix_eq_matrixScalar]
  rfl

private theorem spectrumScalarMatrix_ofNat
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) [Fintype (UConjugates c)]
    [DecidableEq (UConjugates c)] (n : ℕ) [n.AtLeastTwo] :
    spectrumScalarMatrix c (ofNat(n) : ℝ) =
      (ofNat(n) : Matrix (UConjugates c) (UConjugates c) ℝ) := by
  rw [spectrumScalarMatrix_eq_matrixScalar, Matrix.scalar_apply]
  ext i j
  rw [Matrix.ofNat_apply]
  by_cases hij : i = j
  · simp only [Matrix.diagonal_apply, hij, if_pos]
    exact (Nat.cast_ofNat (R := ℝ)).symm
  · simp [hij]

private def spectrumMinimalPolynomial : ℝ[X] :=
  Polynomial.X ^ 4 - 2 * Polynomial.X ^ 3 - 13 * Polynomial.X ^ 2 +
    14 * Polynomial.X + 24

private def spectrumAllOnesPolynomial : ℝ[X] :=
  Polynomial.X ^ 3 + 2 * Polynomial.X ^ 2 - 5 * Polynomial.X - 6

private def spectrumQOnePolynomial : ℝ[X] :=
  3 * (Polynomial.X ^ 2 - Polynomial.X - 12)

private def spectrumQTwoPolynomial : ℝ[X] :=
  Polynomial.X ^ 3 + 3 * Polynomial.X ^ 2 - 16 * Polynomial.X - 48

private def spectrumFactorPolynomial : ℝ[X] :=
  Polynomial.X ^ 2 + Polynomial.C 8 * Polynomial.X + Polynomial.C 15

private noncomputable def spectrumQOne
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) [Fintype (UConjugates c)]
    [DecidableEq (UConjugates c)] :
    Matrix (UConjugates c) (UConjugates c) ℝ :=
  Polynomial.aeval (spectrumAdjMatrix c) spectrumQOnePolynomial

private noncomputable def spectrumQTwo
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) [Fintype (UConjugates c)]
    [DecidableEq (UConjugates c)] :
    Matrix (UConjugates c) (UConjugates c) ℝ :=
  Polynomial.aeval (spectrumAdjMatrix c) spectrumQTwoPolynomial

private theorem spectrum_adj_polynomial
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c)
    [Fintype (UConjugates c)] [DecidableEq (UConjugates c)] :
    let A := spectrumAdjMatrix c
    A ^ 4 - (2 : ℝ) • A ^ 3 - (13 : ℝ) • A ^ 2 +
        (14 : ℝ) • A + spectrumScalarMatrix c 24 = 0 := by
  let A := spectrumAdjMatrix c
  let D₂ := spectrumDistTwoMatrix c
  let D₃ := spectrumDistThreeMatrix c
  have hAA : A * A = spectrumScalarMatrix c 4 + D₂ := by
    exact spectrum_adj_sq hmin c hfirst d
  have hA2 : A ^ 2 = spectrumScalarMatrix c 4 + D₂ := by
    simpa [pow_two] using hAA
  have hAD₂ : A * D₂ = (3 : ℝ) • A + (2 : ℝ) • D₃ := by
    exact spectrum_adj_mul_distTwo hmin c hfirst d
  have hAD₃ : A * D₃ = (3 : ℝ) • D₂ + (2 : ℝ) • D₃ := by
    exact spectrum_adj_mul_distThree hmin c hfirst d
  have hA3 : A ^ 3 = (7 : ℝ) • A + (2 : ℝ) • D₃ := by
    calc
      A ^ 3 = A * (A * A) := by noncomm_ring
      _ = A * (spectrumScalarMatrix c 4 + D₂) := by rw [hAA]
      _ = A * spectrumScalarMatrix c 4 + A * D₂ := by rw [Matrix.mul_add]
      _ = (4 : ℝ) • A + A * D₂ := by rw [mul_spectrumScalarMatrix]
      _ = (7 : ℝ) • A + (2 : ℝ) • D₃ := by rw [hAD₂]; module
  have hA4 : A ^ 4 =
      (7 : ℝ) • (A * A) + (6 : ℝ) • D₂ + (4 : ℝ) • D₃ := by
    calc
      A ^ 4 = A * (A ^ 3) := by noncomm_ring
      _ = A * ((7 : ℝ) • A + (2 : ℝ) • D₃) := by rw [hA3]
      _ = (7 : ℝ) • (A * A) + (2 : ℝ) • (A * D₃) := by
        rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul]
      _ = (7 : ℝ) • (A * A) + (6 : ℝ) • D₂ + (4 : ℝ) • D₃ := by
        rw [hAD₃]
        module
  have hK24 : spectrumScalarMatrix c 24 =
      (6 : ℝ) • spectrumScalarMatrix c 4 := by
    rw [smul_spectrumScalarMatrix]
    norm_num
  dsimp
  rw [hA4, hA3, hA2, hAA, hK24]
  module

private theorem spectrum_allOnes_polynomial
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c)
    [Fintype (UConjugates c)] [DecidableEq (UConjugates c)] :
    let A := spectrumAdjMatrix c
    (2 : ℝ) • spectrumAllOnes c =
      A ^ 3 + (2 : ℝ) • A ^ 2 - (5 : ℝ) • A -
        spectrumScalarMatrix c 6 := by
  let A := spectrumAdjMatrix c
  let D₂ := spectrumDistTwoMatrix c
  let D₃ := spectrumDistThreeMatrix c
  have hAA : A * A = spectrumScalarMatrix c 4 + D₂ :=
    spectrum_adj_sq hmin c hfirst d
  have hA2 : A ^ 2 = spectrumScalarMatrix c 4 + D₂ := by
    simpa [pow_two] using hAA
  have hAD₂ : A * D₂ = (3 : ℝ) • A + (2 : ℝ) • D₃ :=
    spectrum_adj_mul_distTwo hmin c hfirst d
  have hA3 : A ^ 3 = (7 : ℝ) • A + (2 : ℝ) • D₃ := by
    calc
      A ^ 3 = A * (A * A) := by noncomm_ring
      _ = A * (spectrumScalarMatrix c 4 + D₂) := by rw [hAA]
      _ = A * spectrumScalarMatrix c 4 + A * D₂ := by rw [Matrix.mul_add]
      _ = (4 : ℝ) • A + A * D₂ := by rw [mul_spectrumScalarMatrix]
      _ = (7 : ℝ) • A + (2 : ℝ) • D₃ := by rw [hAD₂]; module
  have hpart :
      spectrumScalarMatrix c 1 + A + D₂ + D₃ = spectrumAllOnes c :=
    spectrum_partition c
  calc
    (2 : ℝ) • spectrumAllOnes c =
        (2 : ℝ) • (spectrumScalarMatrix c 1 + A + D₂ + D₃) := by rw [hpart]
    _ = A ^ 3 + (2 : ℝ) • A ^ 2 - (5 : ℝ) • A -
        spectrumScalarMatrix c 6 := by
      rw [hA3, hA2, spectrumScalarMatrix_eq_smul_one c 4,
        spectrumScalarMatrix_eq_smul_one c 6]
      module

private theorem spectrum_eval_minimalPolynomial
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c)
    [Fintype (UConjugates c)] [DecidableEq (UConjugates c)] :
    Polynomial.aeval (spectrumAdjMatrix c) spectrumMinimalPolynomial = 0 := by
  rw [spectrumMinimalPolynomial]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat,
    Polynomial.aeval_X]
  rw [← spectrumScalarMatrix_ofNat c 2,
    ← spectrumScalarMatrix_ofNat c 13,
    ← spectrumScalarMatrix_ofNat c 14,
    ← spectrumScalarMatrix_ofNat c 24,
    spectrumScalarMatrix_mul, spectrumScalarMatrix_mul,
    spectrumScalarMatrix_mul]
  exact spectrum_adj_polynomial hmin c hfirst d

private theorem spectrum_eval_allOnesPolynomial
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c)
    [Fintype (UConjugates c)] [DecidableEq (UConjugates c)] :
    Polynomial.aeval (spectrumAdjMatrix c) spectrumAllOnesPolynomial =
      (2 : ℝ) • spectrumAllOnes c := by
  rw [spectrumAllOnesPolynomial]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat,
    Polynomial.aeval_X]
  rw [← spectrumScalarMatrix_ofNat c 2,
    ← spectrumScalarMatrix_ofNat c 5,
    ← spectrumScalarMatrix_ofNat c 6,
    spectrumScalarMatrix_mul, spectrumScalarMatrix_mul]
  exact (spectrum_allOnes_polynomial hmin c hfirst d).symm

private theorem spectrumQOne_eq
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    [Fintype (UConjugates c)] [DecidableEq (UConjugates c)] :
    spectrumQOne c =
      (3 : ℝ) • (spectrumAdjMatrix c ^ 2 - spectrumAdjMatrix c -
        spectrumScalarMatrix c 12) := by
  rw [spectrumQOne, spectrumQOnePolynomial]
  simp only [map_mul, map_sub, map_pow, map_ofNat, Polynomial.aeval_X]
  rw [← spectrumScalarMatrix_ofNat c 3,
    ← spectrumScalarMatrix_ofNat c 12,
    spectrumScalarMatrix_mul]

private theorem spectrumQTwo_eq
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    [Fintype (UConjugates c)] [DecidableEq (UConjugates c)] :
    spectrumQTwo c =
      spectrumAdjMatrix c ^ 3 + (3 : ℝ) • spectrumAdjMatrix c ^ 2 -
        (16 : ℝ) • spectrumAdjMatrix c - spectrumScalarMatrix c 48 := by
  rw [spectrumQTwo, spectrumQTwoPolynomial]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat,
    Polynomial.aeval_X]
  rw [← spectrumScalarMatrix_ofNat c 3,
    ← spectrumScalarMatrix_ofNat c 16,
    ← spectrumScalarMatrix_ofNat c 48,
    spectrumScalarMatrix_mul, spectrumScalarMatrix_mul]

private theorem spectrum_sumSquares
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c)
    [Fintype (UConjugates c)] [DecidableEq (UConjugates c)] :
    spectrumQOne c * spectrumQOne c + spectrumQTwo c * spectrumQTwo c =
      (180 : ℝ) • (spectrumScalarMatrix c 15 +
        (5 : ℝ) • spectrumAdjMatrix c - spectrumAllOnes c) := by
  let A := spectrumAdjMatrix c
  have hpoly : spectrumQOnePolynomial ^ 2 + spectrumQTwoPolynomial ^ 2 =
      Polynomial.C 180 *
          (Polynomial.C 15 + Polynomial.C 5 * Polynomial.X) -
        Polynomial.C 90 * spectrumAllOnesPolynomial +
        spectrumFactorPolynomial * spectrumMinimalPolynomial := by
    simp [spectrumQOnePolynomial, spectrumQTwoPolynomial,
      spectrumAllOnesPolynomial, spectrumFactorPolynomial,
      spectrumMinimalPolynomial, Polynomial.C_ofNat]
    ring
  have hmap := congrArg
    (fun p : ℝ[X] => Polynomial.aeval A p) hpoly
  have hmap' :
      spectrumQOne c * spectrumQOne c + spectrumQTwo c * spectrumQTwo c =
        algebraMap ℝ (Matrix (UConjugates c) (UConjugates c) ℝ) 180 *
            (algebraMap ℝ (Matrix (UConjugates c) (UConjugates c) ℝ) 15 +
              algebraMap ℝ (Matrix (UConjugates c) (UConjugates c) ℝ) 5 * A) -
          algebraMap ℝ (Matrix (UConjugates c) (UConjugates c) ℝ) 90 *
            Polynomial.aeval A spectrumAllOnesPolynomial +
          Polynomial.aeval A spectrumFactorPolynomial *
            Polynomial.aeval A spectrumMinimalPolynomial := by
    simpa only [spectrumQOne, spectrumQTwo, map_add, map_sub, map_mul,
      map_pow, Polynomial.aeval_C, Polynomial.aeval_X, pow_two] using hmap
  rw [spectrum_eval_minimalPolynomial hmin c hfirst d,
    spectrum_eval_allOnesPolynomial hmin c hfirst d, Matrix.mul_zero,
    add_zero] at hmap'
  rw [← spectrumScalarMatrix_eq_algebraMap c 180,
    ← spectrumScalarMatrix_eq_algebraMap c 15,
    ← spectrumScalarMatrix_eq_algebraMap c 5,
    ← spectrumScalarMatrix_eq_algebraMap c 90,
    spectrumScalarMatrix_mul, spectrumScalarMatrix_mul,
    spectrumScalarMatrix_mul] at hmap'
  calc
    spectrumQOne c * spectrumQOne c + spectrumQTwo c * spectrumQTwo c =
        (180 : ℝ) •
            (spectrumScalarMatrix c 15 + (5 : ℝ) • A) -
          (90 : ℝ) • ((2 : ℝ) • spectrumAllOnes c) := hmap'
    _ = (180 : ℝ) • (spectrumScalarMatrix c 15 +
        (5 : ℝ) • spectrumAdjMatrix c - spectrumAllOnes c) := by
      dsimp [A]
      module

private theorem spectrumAdjMatrix_transpose
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) :
    (spectrumAdjMatrix c)ᵀ = spectrumAdjMatrix c := by
  ext i j
  change spectrumAdjMatrix c j i = spectrumAdjMatrix c i j
  by_cases hij : (commutingGraph c).Adj i j
  · rw [spectrumAdjMatrix_apply_of c i j hij,
      spectrumAdjMatrix_apply_of c j i hij.symm]
  · have hji : ¬ (commutingGraph c).Adj j i := fun h => hij h.symm
    rw [spectrumAdjMatrix_apply_of_not c i j hij,
      spectrumAdjMatrix_apply_of_not c j i hji]

private theorem spectrumScalarMatrix_transpose
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) [Fintype (UConjugates c)] (r : ℝ) :
    (spectrumScalarMatrix c r)ᵀ = spectrumScalarMatrix c r := by
  ext i j
  change spectrumScalarMatrix c r j i = spectrumScalarMatrix c r i j
  by_cases hij : i = j
  · subst j
    rfl
  · have hji : j ≠ i := fun h => hij h.symm
    rw [spectrumScalarMatrix_apply_of_ne c r hij,
      spectrumScalarMatrix_apply_of_ne c r hji]

private theorem spectrumQOne_transpose
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    [Fintype (UConjugates c)] [DecidableEq (UConjugates c)] :
    (spectrumQOne c)ᵀ = spectrumQOne c := by
  rw [spectrumQOne_eq]
  simp [Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_pow,
    spectrumAdjMatrix_transpose, spectrumScalarMatrix_transpose]

private theorem spectrumQTwo_transpose
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    [Fintype (UConjugates c)] [DecidableEq (UConjugates c)] :
    (spectrumQTwo c)ᵀ = spectrumQTwo c := by
  rw [spectrumQTwo_eq]
  simp [Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_add,
    Matrix.transpose_pow, spectrumAdjMatrix_transpose,
    spectrumScalarMatrix_transpose]

private theorem spectrum_sumSquares_transpose
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c)
    [Fintype (UConjugates c)] [DecidableEq (UConjugates c)] :
    (spectrumQOne c)ᵀ * spectrumQOne c +
        (spectrumQTwo c)ᵀ * spectrumQTwo c =
      (180 : ℝ) • (spectrumScalarMatrix c 15 +
        (5 : ℝ) • spectrumAdjMatrix c - spectrumAllOnes c) := by
  rw [spectrumQOne_transpose, spectrumQTwo_transpose]
  exact spectrum_sumSquares hmin c hfirst d

private noncomputable def spectrumIndicator
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (S : Set (UConjugates c)) :
    UConjugates c → ℝ := by
  classical
  exact fun x => if x ∈ S then 1 else 0

private theorem spectrumIndicator_apply_of_mem
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (S : Set (UConjugates c))
    {x : UConjugates c} (hx : x ∈ S) :
    spectrumIndicator c S x = 1 := by
  classical
  simp [spectrumIndicator, hx]

private theorem spectrumIndicator_apply_of_not_mem
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (S : Set (UConjugates c))
    {x : UConjugates c} (hx : x ∉ S) :
    spectrumIndicator c S x = 0 := by
  classical
  simp [spectrumIndicator, hx]

private theorem spectrumIndicator_sum
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) [Fintype (UConjugates c)]
    (S : Set (UConjugates c)) :
    ∑ x, spectrumIndicator c S x = Nat.card S := by
  classical
  rw [Nat.card_eq_fintype_card]
  simp [spectrumIndicator]

private theorem spectrumIndicator_dot_self
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) [Fintype (UConjugates c)]
    (S : Set (UConjugates c)) :
    spectrumIndicator c S ⬝ᵥ spectrumIndicator c S = Nat.card S := by
  classical
  rw [dotProduct]
  calc
    (∑ x, spectrumIndicator c S x * spectrumIndicator c S x) =
        ∑ x, spectrumIndicator c S x := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ∈ S
      · rw [spectrumIndicator_apply_of_mem c S hx]
        norm_num
      · rw [spectrumIndicator_apply_of_not_mem c S hx]
        norm_num
    _ = Nat.card S := spectrumIndicator_sum c S

private theorem spectrumScalarMatrix_mulVec
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) [Fintype (UConjugates c)]
    [DecidableEq (UConjugates c)] (r : ℝ)
    (v : UConjugates c → ℝ) :
    spectrumScalarMatrix c r *ᵥ v = r • v := by
  rw [spectrumScalarMatrix_eq_matrixScalar, Matrix.scalar_apply,
    Matrix.diagonal_const_mulVec]

private theorem spectrumIndicator_scalar_quadratic
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) [Fintype (UConjugates c)]
    [DecidableEq (UConjugates c)] (S : Set (UConjugates c)) (r : ℝ) :
    spectrumIndicator c S ⬝ᵥ
        (spectrumScalarMatrix c r *ᵥ spectrumIndicator c S) =
      r * Nat.card S := by
  rw [spectrumScalarMatrix_mulVec, dotProduct_smul,
    spectrumIndicator_dot_self]
  simp [smul_eq_mul]

private theorem spectrumIndicator_allOnes_quadratic
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) [Fintype (UConjugates c)]
    (S : Set (UConjugates c)) :
    spectrumIndicator c S ⬝ᵥ
        (spectrumAllOnes c *ᵥ spectrumIndicator c S) =
      (Nat.card S : ℝ) ^ 2 := by
  rw [dotProduct]
  have hrow : ∀ i : UConjugates c,
      (spectrumAllOnes c *ᵥ spectrumIndicator c S) i =
        ∑ j, spectrumIndicator c S j := by
    intro i
    simp [Matrix.mulVec, spectrumAllOnes, dotProduct]
  simp_rw [hrow]
  rw [← Finset.sum_mul, spectrumIndicator_sum]
  ring

private theorem spectrumIndicator_adj_quadratic_eq_zero
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) [Fintype (UConjugates c)]
    (S : Set (UConjugates c))
    (hS : (commutingGraph c).IsIndepSet S) :
    spectrumIndicator c S ⬝ᵥ
        (spectrumAdjMatrix c *ᵥ spectrumIndicator c S) = 0 := by
  classical
  rw [spectrumAdjMatrix]
  rw [SimpleGraph.dotProduct_mulVec_adjMatrix]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  by_cases hi : i ∈ S
  · by_cases hj : j ∈ S
    · by_cases hij : i = j
      · subst j
        rw [if_neg (commutingGraph c).irrefl]
      · have hnotAdj : ¬ (commutingGraph c).Adj i j := hS hi hj hij
        rw [if_neg hnotAdj]
    · rw [spectrumIndicator_apply_of_not_mem c S hj]
      simp
  · rw [spectrumIndicator_apply_of_not_mem c S hi]
    simp

private theorem dotProduct_transpose_mul_self
    {V : Type*} [Fintype V]
    (Q : Matrix V V ℝ) (v : V → ℝ) :
    v ⬝ᵥ ((Qᵀ * Q) *ᵥ v) = (Q *ᵥ v) ⬝ᵥ (Q *ᵥ v) := by
  rw [← Matrix.mulVec_mulVec]
  exact Matrix.dotProduct_transpose_mulVec Q v (Q *ᵥ v)

private theorem spectrumIndicator_certificate_quadratic
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) [Fintype (UConjugates c)]
    [DecidableEq (UConjugates c)]
    (S : Set (UConjugates c))
    (hS : (commutingGraph c).IsIndepSet S) :
    spectrumIndicator c S ⬝ᵥ
        ((spectrumScalarMatrix c 15 +
            (5 : ℝ) • spectrumAdjMatrix c - spectrumAllOnes c) *ᵥ
          spectrumIndicator c S) =
      15 * Nat.card S - (Nat.card S : ℝ) ^ 2 := by
  rw [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
    dotProduct_sub, dotProduct_add, dotProduct_smul,
    spectrumIndicator_scalar_quadratic,
    spectrumIndicator_adj_quadratic_eq_zero c S hS,
    spectrumIndicator_allOnes_quadratic]
  ring

private theorem spectrumIndicator_sumSquares_eq
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c)
    [Fintype (UConjugates c)] [DecidableEq (UConjugates c)]
    (S : Set (UConjugates c))
    (hS : (commutingGraph c).IsIndepSet S) :
    (spectrumQOne c *ᵥ spectrumIndicator c S) ⬝ᵥ
          (spectrumQOne c *ᵥ spectrumIndicator c S) +
        (spectrumQTwo c *ᵥ spectrumIndicator c S) ⬝ᵥ
          (spectrumQTwo c *ᵥ spectrumIndicator c S) =
      180 * ((Nat.card S : ℝ) * (15 - Nat.card S)) := by
  let χ := spectrumIndicator c S
  calc
    (spectrumQOne c *ᵥ χ) ⬝ᵥ (spectrumQOne c *ᵥ χ) +
        (spectrumQTwo c *ᵥ χ) ⬝ᵥ (spectrumQTwo c *ᵥ χ) =
        χ ⬝ᵥ (((spectrumQOne c)ᵀ * spectrumQOne c +
          (spectrumQTwo c)ᵀ * spectrumQTwo c) *ᵥ χ) := by
      rw [Matrix.add_mulVec, dotProduct_add,
        dotProduct_transpose_mul_self, dotProduct_transpose_mul_self]
    _ = χ ⬝ᵥ (((180 : ℝ) •
        (spectrumScalarMatrix c 15 + (5 : ℝ) • spectrumAdjMatrix c -
          spectrumAllOnes c)) *ᵥ χ) := by
      rw [spectrum_sumSquares_transpose hmin c hfirst d]
    _ = 180 * ((Nat.card S : ℝ) * (15 - Nat.card S)) := by
      rw [Matrix.smul_mulVec, dotProduct_smul,
        spectrumIndicator_certificate_quadratic c S hS]
      ring

public theorem firstCase_indepSet_card_le_fifteen
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c)
    [Fintype (UConjugates c)] [DecidableEq (UConjugates c)]
    (S : Set (UConjugates c))
    (hS : (commutingGraph c).IsIndepSet S) :
    Nat.card S ≤ 15 := by
  have hsum := spectrumIndicator_sumSquares_eq hmin c hfirst d S hS
  have hq1 : 0 ≤
      (spectrumQOne c *ᵥ spectrumIndicator c S) ⬝ᵥ
        (spectrumQOne c *ᵥ spectrumIndicator c S) := by
    exact Fintype.sum_nonneg fun _ => mul_self_nonneg _
  have hq2 : 0 ≤
      (spectrumQTwo c *ᵥ spectrumIndicator c S) ⬝ᵥ
        (spectrumQTwo c *ᵥ spectrumIndicator c S) := by
    exact Fintype.sum_nonneg fun _ => mul_self_nonneg _
  have hcert : 0 ≤ (Nat.card S : ℝ) * (15 - Nat.card S) := by
    nlinarith
  by_contra hle
  have hsNat : 16 ≤ Nat.card S := by omega
  have hsReal : (16 : ℝ) ≤ Nat.card S := by exact_mod_cast hsNat
  have hsNonneg : 0 ≤ (Nat.card S : ℝ) := by positivity
  nlinarith

private theorem spectrumIndicator_adj_mulVec_apply_eq_card
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) [Fintype (UConjugates c)]
    (S : Set (UConjugates c)) (v : UConjugates c) :
    (spectrumAdjMatrix c *ᵥ spectrumIndicator c S) v =
      Nat.card {x : {x : UConjugates c // x ∈ S} //
        (commutingGraph c).Adj v x.1} := by
  classical
  let e :
      {x // x ∈ ((commutingGraph c).neighborFinset v).filter
        (fun x => x ∈ S)} ≃
        {x : {x : UConjugates c // x ∈ S} //
          (commutingGraph c).Adj v x.1} :=
    { toFun := fun x => ⟨⟨x.1, (Finset.mem_filter.mp x.2).2⟩,
        (SimpleGraph.mem_neighborFinset _ _ _).mp (Finset.mem_filter.mp x.2).1⟩
      invFun := fun x => ⟨x.1.1, Finset.mem_filter.mpr
        ⟨(SimpleGraph.mem_neighborFinset _ _ _).mpr x.2, x.1.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simp only [spectrumAdjMatrix, SimpleGraph.adjMatrix_mulVec_apply]
  calc
    (∑ x ∈ (commutingGraph c).neighborFinset v,
        spectrumIndicator c S x) =
        ∑ x ∈ (commutingGraph c).neighborFinset v,
          if x ∈ S then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ∈ S
      · rw [if_pos hx, spectrumIndicator_apply_of_mem c S hx]
      · rw [if_neg hx, spectrumIndicator_apply_of_not_mem c S hx]
    _ = (((commutingGraph c).neighborFinset v).filter
        (fun x => x ∈ S)).card := by simp
    _ = Fintype.card {x : {x : UConjugates c // x ∈ S} //
        (commutingGraph c).Adj v x.1} := by
      exact_mod_cast (Fintype.card_coe _).symm.trans (Fintype.card_congr e)
    _ = Nat.card {x : {x : UConjugates c // x ∈ S} //
        (commutingGraph c).Adj v x.1} := by
      rw [Nat.card_eq_fintype_card]

private theorem firstCase_commutingGraph_degree_eq_four
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c)
    [Fintype (UConjugates c)]
    [DecidableRel (commutingGraph c).Adj]
    (v : UConjugates c) :
    (commutingGraph c).degree v = 4 := by
  classical
  let e :
      {x // x ∈ (commutingGraph c).neighborFinset v} ≃
        {x : UConjugates c // (commutingGraph c).Adj v x} :=
    { toFun := fun x => ⟨x.1, (SimpleGraph.mem_neighborFinset _ _ _).mp x.2⟩
      invFun := fun x => ⟨x.1, (SimpleGraph.mem_neighborFinset _ _ _).mpr x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc
    (commutingGraph c).degree v =
        ((commutingGraph c).neighborFinset v).card := rfl
    _ = Fintype.card {x // x ∈ (commutingGraph c).neighborFinset v} :=
      (Fintype.card_coe _).symm
    _ = Fintype.card {x : UConjugates c //
        (commutingGraph c).Adj v x} := Fintype.card_congr e
    _ = Nat.card {x : UConjugates c //
        (commutingGraph c).Adj v x} := by rw [Nat.card_eq_fintype_card]
    _ = 4 := firstCase_commutingGraph_degree_four hmin c hfirst d v

private theorem spectrumQOne_indicator_eq_zero_of_card_fifteen
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c)
    [Fintype (UConjugates c)] [DecidableEq (UConjugates c)]
    (S : Set (UConjugates c))
    (hS : (commutingGraph c).IsIndepSet S)
    (hcard : Nat.card S = 15) :
    spectrumQOne c *ᵥ spectrumIndicator c S = 0 := by
  have hsum := spectrumIndicator_sumSquares_eq hmin c hfirst d S hS
  rw [hcard] at hsum
  norm_num at hsum
  have hq1 : 0 ≤
      (spectrumQOne c *ᵥ spectrumIndicator c S) ⬝ᵥ
        (spectrumQOne c *ᵥ spectrumIndicator c S) :=
    Fintype.sum_nonneg fun _ => mul_self_nonneg _
  have hq2 : 0 ≤
      (spectrumQTwo c *ᵥ spectrumIndicator c S) ⬝ᵥ
        (spectrumQTwo c *ᵥ spectrumIndicator c S) :=
    Fintype.sum_nonneg fun _ => mul_self_nonneg _
  have hq1zero :
      (spectrumQOne c *ᵥ spectrumIndicator c S) ⬝ᵥ
        (spectrumQOne c *ᵥ spectrumIndicator c S) = 0 := by
    nlinarith
  exact dotProduct_self_eq_zero.mp hq1zero

public theorem firstCase_indepSet_card_fifteen_outside_neighbors
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c)
    [Fintype (UConjugates c)] [DecidableEq (UConjugates c)]
    (S : Set (UConjugates c))
    (hS : (commutingGraph c).IsIndepSet S)
    (hcard : Nat.card S = 15)
    (v : UConjugates c) (hv : v ∉ S) :
    Nat.card {x : UConjugates c //
      x ∈ S ∧ (commutingGraph c).Adj v x} = 3 := by
  classical
  let A := spectrumAdjMatrix c
  let χ := spectrumIndicator c S
  have hQ : spectrumQOne c *ᵥ χ = 0 :=
    spectrumQOne_indicator_eq_zero_of_card_fifteen
      hmin c hfirst d S hS hcard
  rw [spectrumQOne_eq, Matrix.smul_mulVec] at hQ
  have hB : (A ^ 2 - A - spectrumScalarMatrix c 12) *ᵥ χ = 0 := by
    funext x
    have hx := congrFun hQ x
    simp only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hx ⊢
    nlinarith
  have hB' :
      A *ᵥ (A *ᵥ χ) - A *ᵥ χ - (12 : ℝ) • χ = 0 := by
    rw [Matrix.sub_mulVec, Matrix.sub_mulVec, pow_two,
      ← Matrix.mulVec_mulVec, spectrumScalarMatrix_mulVec] at hB
    exact hB
  have hdiff :
      A *ᵥ (A *ᵥ χ) - A *ᵥ χ = (12 : ℝ) • χ :=
    sub_eq_zero.mp hB'
  have hA2χ :
      A *ᵥ (A *ᵥ χ) = A *ᵥ χ + (12 : ℝ) • χ := by
    calc
      A *ᵥ (A *ᵥ χ) =
          (A *ᵥ (A *ᵥ χ) - A *ᵥ χ) + A *ᵥ χ := by abel
      _ = (12 : ℝ) • χ + A *ᵥ χ := by rw [hdiff]
      _ = A *ᵥ χ + (12 : ℝ) • χ := by abel
  let y : UConjugates c → ℝ := A *ᵥ χ + (3 : ℝ) • χ
  have hAy : A *ᵥ y = (4 : ℝ) • y := by
    dsimp [y]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, hA2χ]
    module
  have hLap : (commutingGraph c).lapMatrix ℝ *ᵥ y = 0 := by
    funext x
    rw [SimpleGraph.lapMatrix_mulVec_apply,
      firstCase_commutingGraph_degree_eq_four hmin c hfirst d x]
    have hx := congrFun hAy x
    simp only [A, spectrumAdjMatrix,
      SimpleGraph.adjMatrix_mulVec_apply, Pi.smul_apply, smul_eq_mul] at hx
    rw [hx]
    norm_num
  have hconst : ∀ a b : UConjugates c, y a = y b := by
    have hreached :=
      ((commutingGraph c).lapMatrix_mulVec_eq_zero_iff_forall_reachable).mp hLap
    intro a b
    exact hreached a b (firstCase_commutingGraph_connected
      hmin c hfirst d a b)
  have hpos : 0 < Nat.card S := by rw [hcard]; norm_num
  obtain ⟨x⟩ := (Nat.card_pos_iff.mp hpos).1
  have hinsideCard : Nat.card {z : {z : UConjugates c // z ∈ S} //
      (commutingGraph c).Adj x.1 z.1} = 0 := by
    rw [Nat.card_eq_zero]
    left
    constructor
    intro z
    have hxz : x.1 ≠ z.1.1 := by
      intro hxz
      apply (commutingGraph c).irrefl
      simpa only [hxz] using z.2
    exact (hS x.2 z.1.2 hxz) z.2
  have hAx : (A *ᵥ χ) x.1 = 0 := by
    change (spectrumAdjMatrix c *ᵥ spectrumIndicator c S) x.1 = 0
    rw [spectrumIndicator_adj_mulVec_apply_eq_card c S x.1, hinsideCard]
    norm_num
  have hχx : χ x.1 = 1 := by
    exact spectrumIndicator_apply_of_mem c S x.2
  have hyx : y x.1 = 3 := by
    dsimp [y]
    rw [hAx, hχx]
    norm_num
  have hyv : y v = 3 := (hconst v x.1).trans hyx
  have hχv : χ v = 0 := by
    exact spectrumIndicator_apply_of_not_mem c S hv
  have hAv : (A *ᵥ χ) v = 3 := by
    dsimp [y] at hyv
    rw [hχv] at hyv
    nlinarith
  have hcountReal :
      (Nat.card {z : {z : UConjugates c // z ∈ S} //
        (commutingGraph c).Adj v z.1} : ℝ) = 3 := by
    calc
      (Nat.card {z : {z : UConjugates c // z ∈ S} //
          (commutingGraph c).Adj v z.1} : ℝ) =
          (A *ᵥ χ) v := by
        exact (spectrumIndicator_adj_mulVec_apply_eq_card c S v).symm
      _ = 3 := hAv
  have hcountNested : Nat.card {z : {z : UConjugates c // z ∈ S} //
      (commutingGraph c).Adj v z.1} = 3 := by
    exact_mod_cast hcountReal
  let e :
      {z : {z : UConjugates c // z ∈ S} //
        (commutingGraph c).Adj v z.1} ≃
      {z : UConjugates c // z ∈ S ∧ (commutingGraph c).Adj v z} :=
    { toFun := fun z => ⟨z.1.1, And.intro z.1.2 z.2⟩
      invFun := fun z => ⟨⟨z.1, z.2.1⟩, z.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc
    Nat.card {z : UConjugates c //
        z ∈ S ∧ (commutingGraph c).Adj v z} =
        Nat.card {z : {z : UConjugates c // z ∈ S} //
          (commutingGraph c).Adj v z.1} := (Nat.card_congr e).symm
    _ = 3 := hcountNested

end

end CFSG.GorensteinWalter
