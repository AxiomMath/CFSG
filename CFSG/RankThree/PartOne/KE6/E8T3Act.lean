module

public import CFSG.RankThree.PartOne.KE6.E8T3Tables
public import CFSG.RankThree.PartOne.KE.D4TranspositionInterface

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Lattice
  CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.PartOne.KE (d4Nodes)

variable {T : WeylGroup Tag.E8}

theorem colT_supp_of_maps {J : Finset (Fin Tag.E8.rank)}
    (hmaps : ∀ β ∈ parabolicRoots Tag.E8 (↑J : Set (Fin Tag.E8.rank)),
      T • β ∈ parabolicRoots Tag.E8 ↑J) :
    ∀ j ∈ J, ∀ i, i ∉ J → colT T j i = 0 := fun j hj i hi => by
  have hmem : (Pi.single j 1 : V8) ∈ parabolicRoots Tag.E8 (↑J : Set (Fin Tag.E8.rank)) :=
    ⟨isRoot_single Tag.E8 j, fun i hi' => Pi.single_eq_of_ne
      (fun h : i = j => hi' (by rw [h]; exact Finset.mem_coe.2 hj)) 1⟩
  exact (hmaps _ hmem).2 i (by simpa using hi)

theorem cols_mem_of_search (hrel : ∀ x : V8, T • T • x + T • x + x = 0)
    (js : List (Fin Tag.E8.rank)) (hnd : js.Nodup)
    (hsupp : ∀ j ∈ js, ∀ i, i ∉ js → colT T j i = 0) (S : List (List V8))
    (h : tsearch (e8RootsIn js) js [] (fun part => !relOK part || (part.map Prod.snd ∈ S)) = true) :
    js.map (colT T) ∈ S := by
  have h1 := tsearch_colT hrel js hsupp _ h
  rw [relOK_colT hrel js hnd hsupp] at h1
  simp only [Bool.not_true, Bool.false_or, decide_eq_true_eq] at h1
  rw [List.map_map] at h1
  exact h1

theorem e8Edges_ne : ∀ e ∈ e8Edges, e.1 ≠ e.2 := by decide

set_option maxRecDepth 100000 in
theorem e8TwoA2_nodup : ∀ q ∈ e8TwoA2,
    [q.1, q.2.1, q.2.2.1, q.2.2.2].Nodup := by decide +kernel

theorem e8T3_cols_A2 (hrel : ∀ x : V8, T • T • x + T • x + x = 0)
    {a b : Fin Tag.E8.rank} (hab : (a, b) ∈ e8Edges)
    (hmaps : ∀ β ∈ parabolicRoots Tag.E8 (↑({a, b} : Finset (Fin Tag.E8.rank)) :
      Set (Fin Tag.E8.rank)), T • β ∈ parabolicRoots Tag.E8 ↑({a, b} : Finset (Fin Tag.E8.rank))) :
    [colT T a, colT T b] ∈ rotCols a b := by
  have hne : a ≠ b := e8Edges_ne _ hab
  have hsupp := colT_supp_of_maps hmaps
  exact cols_mem_of_search hrel [a, b] (by simp [hne]) (fun j hj i hi => hsupp j (by simpa using hj) i
    (by simpa using hi)) _ (e8T3_search_A2 (a, b) hab)

theorem e8T3_cols_2A2 (hrel : ∀ x : V8, T • T • x + T • x + x = 0)
    {a b c d : Fin Tag.E8.rank} (h : (a, b, c, d) ∈ e8TwoA2)
    (hmaps : ∀ β ∈ parabolicRoots Tag.E8 (↑({a, b, c, d} : Finset (Fin Tag.E8.rank)) :
      Set (Fin Tag.E8.rank)),
      T • β ∈ parabolicRoots Tag.E8 ↑({a, b, c, d} : Finset (Fin Tag.E8.rank))) :
    [colT T a, colT T b, colT T c, colT T d] ∈ rot2Cols a b c d := by
  have hnd := e8TwoA2_nodup _ h
  have hsupp := colT_supp_of_maps hmaps
  exact cols_mem_of_search hrel [a, b, c, d] hnd (fun j hj i hi => hsupp j (by simpa using hj) i
    (by simpa using hi)) _ (e8T3_search_2A2 (a, b, c, d) h)

theorem e8T3_cols_D4 (hrel : ∀ x : V8, T • T • x + T • x + x = 0)
    (hmaps : ∀ β ∈ parabolicRoots Tag.E8 (↑({1, 2, 3, 4} : Finset (Fin Tag.E8.rank)) :
      Set (Fin Tag.E8.rank)),
      T • β ∈ parabolicRoots Tag.E8 ↑({1, 2, 3, 4} : Finset (Fin Tag.E8.rank))) :
    [colT T 1, colT T 2, colT T 3, colT T 4] ∈ d4Cols := by
  have hsupp := colT_supp_of_maps hmaps
  exact cols_mem_of_search hrel [1, 2, 3, 4] (by decide) (fun j hj i hi => hsupp j (by simpa using hj) i
    (by simpa using hi)) _ e8T3_search_D4

theorem e8T3_cols_D4A2 (hrel : ∀ x : V8, T • T • x + T • x + x = 0)
    (hmaps : ∀ β ∈ parabolicRoots Tag.E8 (↑({1, 2, 3, 4, 6, 7} : Finset (Fin Tag.E8.rank)) :
      Set (Fin Tag.E8.rank)),
      T • β ∈ parabolicRoots Tag.E8 ↑({1, 2, 3, 4, 6, 7} : Finset (Fin Tag.E8.rank))) :
    [colT T 1, colT T 2, colT T 3, colT T 4, colT T 6, colT T 7] ∈ d4a2Cols := by
  have hsupp := colT_supp_of_maps hmaps
  exact cols_mem_of_search hrel [1, 2, 3, 4, 6, 7] (by decide) (fun j hj i hi => hsupp j
    (by simpa using hj) i (by simpa using hi)) _ e8T3_search_D4A2

@[expose] def colsApply (js : List (Fin Tag.E8.rank)) (cols : List V8) (x : V8) : V8 :=
  (js.zip cols).foldl (fun (acc : V8) q => acc + x q.1 • q.2) (0 : V8)

theorem colsApply_colT (js : List (Fin Tag.E8.rank)) (hnd : js.Nodup) (x : V8)
    (hx : ∀ i, i ∉ js → x i = 0) : colsApply js (js.map (colT T)) x = T • x := by
  rw [colsApply, zip_map_self, List.foldl_map]
  exact foldl_colT_eq_smul js hnd x hx

set_option maxRecDepth 100000 in
theorem e8D4Table_ok : ∀ ent ∈ e8D4Table, ∀ l ∈ Tag.E8.artifactRoots,
    (∀ i, i ∉ ([1, 2, 3, 4] : List (Fin Tag.E8.rank)) → toVec Tag.E8.rank l i = 0) →
    colsApply [1, 2, 3, 4] (ent.1.map (toVec Tag.E8.rank)) (toVec Tag.E8.rank l) =
      ent.2.1.foldr (reflect Tag.E8) (permLattice
        (List.formPerm [ent.2.2.2.1, ent.2.2.2.2.1, ent.2.2.2.2.2]) (toVec Tag.E8.rank l)) ∧
    -colsApply [1, 2, 3, 4] (ent.1.map (toVec Tag.E8.rank)) (toVec Tag.E8.rank l) =
      ent.2.2.1.foldr (reflect Tag.E8) (permLattice
        (List.formPerm [ent.2.2.2.1, ent.2.2.2.2.1, ent.2.2.2.2.2]) (toVec Tag.E8.rank l)) := by
  decide +kernel

theorem e8D4Table_leaves : ∀ ent ∈ e8D4Table,
    ent.2.2.2.1 ≠ ent.2.2.2.2.1 ∧ ent.2.2.2.2.1 ≠ ent.2.2.2.2.2 ∧ ent.2.2.2.1 ≠ ent.2.2.2.2.2 ∧
    ent.2.2.2.1.val ∈ ({1, 2, 4} : Set ℕ) ∧ ent.2.2.2.2.1.val ∈ ({1, 2, 4} : Set ℕ) ∧
    ent.2.2.2.2.2.val ∈ ({1, 2, 4} : Set ℕ) ∧ (∀ i ∈ ent.2.1, i ∈ d4Nodes Tag.E8) ∧
    (∀ i ∈ ent.2.2.1, i ∈ d4Nodes Tag.E8) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, d4Nodes, Set.mem_ofPred_eq]
  decide +kernel

theorem coe_d4_finset : (↑({1, 2, 3, 4} : Finset (Fin Tag.E8.rank)) : Set (Fin Tag.E8.rank)) =
    d4Nodes Tag.E8 := by
  ext i
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff,
    d4Nodes, Set.mem_ofPred_eq]
  revert i
  decide +kernel

theorem mem_d4Nodes_iff (i : Fin Tag.E8.rank) :
    i ∈ d4Nodes Tag.E8 ↔ i ∈ ([1, 2, 3, 4] : List (Fin Tag.E8.rank)) := by
  simp only [d4Nodes, Set.mem_ofPred_eq]
  revert i
  decide +kernel

theorem e8T3_D4_cert (hcols : [colT T 1, colT T 2, colT T 3, colT T 4] ∈ d4Cols)
    {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) :
    ∃ a b c : Fin Tag.E8.rank, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ a.val ∈ ({1, 2, 4} : Set ℕ) ∧
      b.val ∈ ({1, 2, 4} : Set ℕ) ∧ c.val ∈ ({1, 2, 4} : Set ℕ) ∧
      ∃ u ∈ parabolicWeylGroup Tag.E8 (d4Nodes Tag.E8), ∀ α ∈ parabolicRoots Tag.E8 (d4Nodes Tag.E8),
        σ • (T • α) = u • permLattice (List.formPerm [a, b, c]) α := by
  obtain ⟨ent, hent, hcol⟩ : ∃ ent ∈ e8D4Table,
      ent.1.map (toVec Tag.E8.rank) = [colT T 1, colT T 2, colT T 3, colT T 4] := by
    simp only [d4Cols, List.mem_map] at hcols
    obtain ⟨ent, hent, h⟩ := hcols
    exact ⟨ent, hent, h⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := e8D4Table_leaves ent hent
  refine ⟨_, _, _, h1, h2, h3, h4, h5, h6, ?_⟩
  have hok := e8D4Table_ok ent hent
  have hmk : ∀ (l : List ℤ), l ∈ Tag.E8.artifactRoots → IsRoot Tag.E8 (toVec Tag.E8.rank l) →
      (∀ i, i ∉ d4Nodes Tag.E8 → toVec Tag.E8.rank l i = 0) →
      T • toVec Tag.E8.rank l = ent.2.1.foldr (reflect Tag.E8) (permLattice
        (List.formPerm [ent.2.2.2.1, ent.2.2.2.2.1, ent.2.2.2.2.2]) (toVec Tag.E8.rank l)) ∧
      -(T • toVec Tag.E8.rank l) = ent.2.2.1.foldr (reflect Tag.E8) (permLattice
        (List.formPerm [ent.2.2.2.1, ent.2.2.2.2.1, ent.2.2.2.2.2]) (toVec Tag.E8.rank l)) := by
    intro l hl _ hsupp
    have hsupp' : ∀ i, i ∉ ([1, 2, 3, 4] : List (Fin Tag.E8.rank)) →
        toVec Tag.E8.rank l i = 0 := fun i hi => hsupp i (fun hh => hi ((mem_d4Nodes_iff i).1 hh))
    obtain ⟨hA, hB⟩ := hok l hl hsupp'
    rw [hcol] at hA hB
    have hc : ([colT T 1, colT T 2, colT T 3, colT T 4] : List V8) =
        ([1, 2, 3, 4] : List (Fin Tag.E8.rank)).map (colT T) := rfl
    rw [hc, colsApply_colT _ (by decide) _ hsupp'] at hA hB
    exact ⟨hA, hB⟩
  rcases hσ with rfl | rfl
  · refine ⟨(coxeterSystem Tag.E8).wordProd ent.2.1, wordProd_mem_parabolicWeylGroup h7, ?_⟩
    intro α hα
    obtain ⟨l, hl, rfl⟩ := isRoot_iff_exists_mem.1 hα.1
    rw [one_smul, wordProd_smul]
    exact (hmk l hl hα.1 hα.2).1
  · refine ⟨(coxeterSystem Tag.E8).wordProd ent.2.2.1, wordProd_mem_parabolicWeylGroup h8, ?_⟩
    intro α hα
    obtain ⟨l, hl, rfl⟩ := isRoot_iff_exists_mem.1 hα.1
    rw [neg_one_smul, wordProd_smul]
    exact (hmk l hl hα.1 hα.2).2

end CFSG.RankThree.PartOne.KE6
