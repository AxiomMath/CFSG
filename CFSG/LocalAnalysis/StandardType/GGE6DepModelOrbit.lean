module

public import CFSG.LocalAnalysis.StandardType.GGE6DepModelDefs

public section

namespace CFSG.StandardType

namespace E6Dep

private def evalVec {n : ℕ} (g : Fin n → Mat6) (x : Vec6) : List (Fin n) → Vec6
  | [] => x
  | i :: l => (g i).mulVec (evalVec g x l)

private lemma evalWord_mulVec {n : ℕ} (g : Fin n → Mat6) (x : Vec6) (l : List (Fin n)) :
    (evalWord g l).mulVec x = evalVec g x l := by
  induction l with
  | nil =>
      show (1 : Mat6).mulVec x = x
      exact Matrix.one_mulVec x
  | cons i l ih =>
      show ((g i) * evalWord g l).mulVec x = (g i).mulVec (evalVec g x l)
      rw [← Matrix.mulVec_mulVec x (g i) (evalWord g l), ih]

private lemma exists_word_of_mem_map_fst {n : ℕ} (g : Fin n → Mat6) (s : Vec6)
    (tab : List (Vec6 × List (Fin n)))
    (hchk : tab.all (fun q => decide (evalVec g s q.2 = q.1)) = true)
    {v : Vec6} (hv : v ∈ tab.map Prod.fst) :
    ∃ word : List (Fin n), (evalWord g word).mulVec s = v := by
  obtain ⟨q, hq, hfq⟩ := List.exists_of_mem_map hv
  refine ⟨q.2, ?_⟩
  simp only [List.all_eq_true] at hchk
  have hvec : evalVec g s q.2 = q.1 := of_decide_eq_true (hchk q hq)
  exact (evalWord_mulVec g s q.2).trans (hvec.trans hfq)

private def t1w2Chunk0 : List (Vec6 × List (Fin 7)) :=
[(![0, 0, 0, 0, 0, 1], []),
 (![2, 1, 0, 0, 0, 2], [6]),
 (![2, 1, 1, 0, 0, 2], [2, 6]),
 (![2, 2, 1, 0, 0, 2], [1, 2, 6]),
 (![2, 1, 1, 1, 0, 2], [3, 2, 6]),
 (![1, 2, 1, 0, 1, 2], [5, 2, 6]),
 (![0, 2, 1, 0, 0, 2], [0, 1, 2, 6]),
 (![2, 2, 1, 1, 0, 2], [3, 1, 2, 6]),
 (![1, 0, 1, 0, 1, 2], [5, 1, 2, 6]),
 (![0, 0, 1, 2, 0, 2], [4, 3, 2, 6]),
 (![1, 2, 1, 1, 1, 2], [5, 3, 2, 6]),
 (![0, 2, 1, 1, 0, 2], [3, 0, 1, 2, 6]),
 (![2, 0, 1, 0, 1, 2], [5, 0, 1, 2, 6]),
 (![2, 2, 2, 1, 0, 2], [2, 3, 1, 2, 6]),
 (![0, 1, 1, 2, 0, 2], [4, 3, 1, 2, 6]),
 (![1, 0, 1, 1, 1, 2], [5, 3, 1, 2, 6]),
 (![1, 0, 2, 0, 1, 2], [2, 5, 1, 2, 6]),
 (![2, 1, 1, 2, 1, 2], [5, 4, 3, 2, 6]),
 (![1, 2, 2, 1, 1, 2], [2, 5, 3, 2, 6]),
 (![0, 2, 2, 1, 0, 2], [2, 3, 0, 1, 2, 6])]

private def wlChunk0 : List (Vec6 × List (Fin 6)) :=
[(![2, 1, 0, 0, 1, 0], []),
 (![2, 1, 1, 0, 1, 0], [2]),
 (![1, 2, 0, 0, 2, 0], [5]),
 (![2, 2, 1, 0, 1, 0], [1, 2]),
 (![2, 1, 1, 1, 1, 0], [3, 2]),
 (![0, 0, 1, 0, 0, 0], [5, 2]),
 (![1, 2, 2, 0, 2, 0], [2, 5]),
 (![0, 2, 1, 0, 1, 0], [0, 1, 2]),
 (![2, 2, 1, 1, 1, 0], [3, 1, 2]),
 (![0, 1, 1, 0, 0, 0], [5, 1, 2]),
 (![0, 0, 1, 2, 1, 0], [4, 3, 2]),
 (![0, 0, 1, 1, 0, 0], [5, 3, 2]),
 (![0, 0, 2, 0, 0, 0], [2, 5, 2]),
 (![1, 1, 2, 0, 2, 0], [1, 2, 5]),
 (![1, 2, 2, 2, 2, 0], [3, 2, 5]),
 (![0, 2, 1, 1, 1, 0], [3, 0, 1, 2]),
 (![1, 1, 1, 0, 0, 0], [5, 0, 1, 2]),
 (![2, 2, 2, 1, 1, 0], [2, 3, 1, 2]),
 (![0, 1, 1, 2, 1, 0], [4, 3, 1, 2]),
 (![0, 1, 1, 1, 0, 0], [5, 3, 1, 2]),
 (![0, 1, 0, 0, 0, 0], [2, 5, 1, 2]),
 (![1, 2, 1, 2, 0, 0], [5, 4, 3, 2]),
 (![0, 0, 0, 1, 0, 0], [2, 5, 3, 2]),
 (![0, 2, 2, 0, 0, 0], [1, 2, 5, 2]),
 (![0, 0, 2, 2, 0, 0], [3, 2, 5, 2]),
 (![0, 1, 2, 0, 2, 0], [0, 1, 2, 5])]

private def wlChunk1 : List (Vec6 × List (Fin 6)) :=
[(![1, 1, 2, 2, 2, 0], [3, 1, 2, 5]),
 (![0, 0, 2, 1, 2, 0], [4, 3, 2, 5]),
 (![0, 2, 2, 1, 1, 0], [2, 3, 0, 1, 2]),
 (![1, 1, 1, 2, 1, 0], [4, 3, 0, 1, 2]),
 (![1, 1, 1, 1, 0, 0], [5, 3, 0, 1, 2]),
 (![1, 1, 0, 0, 0, 0], [2, 5, 0, 1, 2]),
 (![0, 1, 2, 2, 1, 0], [4, 2, 3, 1, 2]),
 (![1, 0, 1, 2, 0, 0], [5, 4, 3, 1, 2]),
 (![0, 2, 0, 0, 0, 0], [1, 2, 5, 1, 2]),
 (![1, 2, 0, 2, 0, 0], [2, 5, 4, 3, 2]),
 (![0, 0, 0, 2, 0, 0], [3, 2, 5, 3, 2]),
 (![2, 2, 2, 0, 0, 0], [0, 1, 2, 5, 2]),
 (![0, 2, 2, 2, 0, 0], [3, 1, 2, 5, 2]),
 (![2, 1, 2, 1, 0, 0], [4, 3, 2, 5, 2]),
 (![0, 1, 2, 2, 2, 0], [3, 0, 1, 2, 5]),
 (![1, 1, 1, 2, 2, 0], [2, 3, 1, 2, 5])]

private def wlChunk2 : List (Vec6 × List (Fin 6)) :=
[(![0, 2, 2, 1, 2, 0], [4, 3, 1, 2, 5]),
 (![0, 0, 2, 1, 1, 0], [1, 2, 3, 0, 1, 2]),
 (![1, 1, 2, 2, 1, 0], [4, 2, 3, 0, 1, 2]),
 (![2, 0, 1, 2, 0, 0], [5, 4, 3, 0, 1, 2]),
 (![1, 0, 0, 0, 0, 0], [1, 2, 5, 0, 1, 2]),
 (![0, 1, 2, 0, 1, 0], [3, 4, 2, 3, 1, 2]),
 (![2, 2, 0, 0, 0, 0], [0, 1, 2, 5, 1, 2]),
 (![1, 2, 0, 1, 0, 0], [3, 2, 5, 4, 3, 2]),
 (![2, 1, 0, 1, 0, 0], [4, 3, 2, 5, 3, 2]),
 (![2, 2, 2, 2, 0, 0], [3, 0, 1, 2, 5, 2]),
 (![2, 0, 2, 1, 0, 0], [4, 3, 1, 2, 5, 2]),
 (![0, 1, 1, 2, 2, 0], [2, 3, 0, 1, 2, 5]),
 (![2, 2, 2, 1, 2, 0], [4, 3, 0, 1, 2, 5])]

private def wlChunk3 : List (Vec6 × List (Fin 6)) :=
[(![0, 2, 1, 1, 2, 0], [4, 2, 3, 1, 2, 5]),
 (![1, 2, 2, 2, 1, 0], [4, 1, 2, 3, 0, 1, 2]),
 (![1, 1, 2, 0, 1, 0], [3, 4, 2, 3, 0, 1, 2]),
 (![2, 0, 0, 0, 0, 0], [0, 1, 2, 5, 0, 1, 2]),
 (![2, 1, 0, 2, 0, 0], [4, 3, 2, 5, 4, 3, 2]),
 (![1, 0, 2, 1, 0, 0], [4, 3, 0, 1, 2, 5, 2]),
 (![0, 0, 1, 2, 2, 0], [1, 2, 3, 0, 1, 2, 5]),
 (![2, 2, 1, 1, 2, 0], [4, 2, 3, 0, 1, 2, 5]),
 (![0, 2, 1, 0, 2, 0], [3, 4, 2, 3, 1, 2, 5]),
 (![1, 2, 2, 0, 1, 0], [3, 4, 1, 2, 3, 0, 1, 2]),
 (![2, 1, 1, 1, 2, 0], [4, 1, 2, 3, 0, 1, 2, 5])]

private def wlChunk4 : List (Vec6 × List (Fin 6)) :=
[(![2, 2, 1, 0, 2, 0], [3, 4, 2, 3, 0, 1, 2, 5]),
 (![1, 2, 0, 0, 1, 0], [2, 3, 4, 1, 2, 3, 0, 1, 2]),
 (![2, 1, 1, 0, 2, 0], [3, 4, 1, 2, 3, 0, 1, 2, 5]),
 (![0, 0, 0, 0, 2, 0], [5, 2, 3, 4, 1, 2, 3, 0, 1, 2]),
 (![2, 1, 0, 0, 2, 0], [2, 3, 4, 1, 2, 3, 0, 1, 2, 5]),
 (![0, 0, 0, 0, 1, 0], [5, 2, 3, 4, 1, 2, 3, 0, 1, 2, 5])]

private def tabWL : List (Vec6 × List (Fin 6)) :=
wlChunk0 ++ wlChunk1 ++ wlChunk2 ++ wlChunk3 ++ wlChunk4

private lemma wlChunk0_ok :
    (wlChunk0).all (fun q => decide (evalVec gensL hB q.2 = q.1)) = true := by
  decide +kernel

private lemma wlChunk1_ok :
    (wlChunk1).all (fun q => decide (evalVec gensL hB q.2 = q.1)) = true := by
  decide +kernel

private lemma wlChunk2_ok :
    (wlChunk2).all (fun q => decide (evalVec gensL hB q.2 = q.1)) = true := by
  decide +kernel

private lemma wlChunk3_ok :
    (wlChunk3).all (fun q => decide (evalVec gensL hB q.2 = q.1)) = true := by
  decide +kernel

private lemma wlChunk4_ok :
    (wlChunk4).all (fun q => decide (evalVec gensL hB q.2 = q.1)) = true := by
  decide +kernel

private lemma allWL :
    tabWL.all (fun q => decide (evalVec gensL hB q.2 = q.1)) = true := by
  simp only [tabWL, List.all_append, wlChunk0_ok, wlChunk1_ok, wlChunk2_ok, wlChunk3_ok, wlChunk4_ok, Bool.and_true, Bool.true_and]

private lemma coverWL : ∀ v : Vec6, norm6 v = 1 → v 5 = 0 → v ∈ tabWL.map Prod.fst := by
  decide +kernel

theorem norm1_perp_orbit_WL (v : Vec6) (hv : norm6 v = 1) (hx : v 5 = 0) :
    ∃ word : List (Fin 6), (evalWord gensL word).mulVec hB = v := by
  exact exists_word_of_mem_map_fst gensL hB tabWL allWL (coverWL v hv hx)

end E6Dep

end CFSG.StandardType

end
