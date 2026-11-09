module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNine3CModel

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NF3C

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts Subgroup

theorem mlGen_codes : [ι46 gAdd, ι46 gSq, ι46 gInv].map (codeN 46) = mlGenC := by
  decide +kernel

theorem ml_one : List.range 46 ∈ mlLit := by decide +kernel

theorem ml_length : mlLit.length = 1080 := by decide +kernel

private def ml_row (i : ℕ) : Bool :=
  (List.range mlGenC.length).all fun k =>
    decide ((mlTbl.getD i []).getD k 0 < mlLit.length) &&
      (Core.cmul (mlLit.getD i (List.range 46)) (mlGenC.getD k (List.range 46)) ==
        mlLit.getD ((mlTbl.getD i []).getD k 0) (List.range 46))

private theorem ml_chunk_all (f : ℕ → Bool) (m : ℕ) : ∀ K : ℕ,
    (∀ k < K, (List.range' (k * m) m).all f = true) → (List.range (K * m)).all f = true
  | 0, _ => by simp
  | K + 1, h => by
    rw [Nat.succ_mul, List.range_add, List.all_append, Bool.and_eq_true]
    refine ⟨ml_chunk_all f m K (fun k hk => h k (by omega)), ?_⟩
    rw [← List.range'_eq_map_range]
    exact h K (by omega)

private theorem ml_tbl_0 : (List.range' (0 * 135) 135).all ml_row = true := by
  decide +kernel

private theorem ml_tbl_1 : (List.range' (1 * 135) 135).all ml_row = true := by
  decide +kernel

private theorem ml_tbl_2 : (List.range' (2 * 135) 135).all ml_row = true := by
  decide +kernel

private theorem ml_tbl_3 : (List.range' (3 * 135) 135).all ml_row = true := by
  decide +kernel

private theorem ml_tbl_4 : (List.range' (4 * 135) 135).all ml_row = true := by
  decide +kernel

private theorem ml_tbl_5 : (List.range' (5 * 135) 135).all ml_row = true := by
  decide +kernel

private theorem ml_tbl_6 : (List.range' (6 * 135) 135).all ml_row = true := by
  decide +kernel

private theorem ml_tbl_7 : (List.range' (7 * 135) 135).all ml_row = true := by
  decide +kernel

theorem ml_tbl : Core.tblCheckC (List.range 46) mlGenC mlLit mlTbl = true := by
  show (List.range mlLit.length).all ml_row = true
  rw [ml_length]
  refine ml_chunk_all ml_row 135 8 (fun k hk => ?_)
  match k, hk with
  | 0, _ => exact ml_tbl_0
  | 1, _ => exact ml_tbl_1
  | 2, _ => exact ml_tbl_2
  | 3, _ => exact ml_tbl_3
  | 4, _ => exact ml_tbl_4
  | 5, _ => exact ml_tbl_5
  | 6, _ => exact ml_tbl_6
  | 7, _ => exact ml_tbl_7
  | n + 8, h => exact absurd h (by omega)

theorem map_ML : ML.map ι46 = closure {g | g ∈ [ι46 gAdd, ι46 gSq, ι46 gInv]} := by
  rw [ML, MonoidHom.map_closure]
  congr 1
  ext g
  simp

theorem card_ML_le : Nat.card ML ≤ 1080 := by
  rw [← card_map_of_injective ι46_injective, map_ML, ← ml_length]
  exact card_closure_le_of_tbl mlGen_codes ml_one ml_tbl


theorem card_GP_le : Nat.card GP ≤ 2160 := by
  have h := card_closure_le_of_cosets ML {gAdd, gSq, gInv, gMul} [1, gMul] (by simp) (by
    intro r hr g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hr with rfl | rfl <;> rcases hg with rfl | rfl | rfl | rfl
    · exact ⟨1, by simp, mem_ML_of_eq [0] (by decide +kernel)⟩
    · exact ⟨1, by simp, mem_ML_of_eq [1] (by decide +kernel)⟩
    · exact ⟨1, by simp, mem_ML_of_eq [2] (by decide +kernel)⟩
    · exact ⟨gMul, by simp, mem_ML_of_eq [] (by decide +kernel)⟩
    · exact ⟨gMul, by simp, mem_ML_of_eq [0, 1, 0, 0, 1, 1, 1] (by decide +kernel)⟩
    · exact ⟨gMul, by simp, mem_ML_of_eq [1] (by decide +kernel)⟩
    · exact ⟨gMul, by simp, mem_ML_of_eq [1, 2] (by decide +kernel)⟩
    · exact ⟨1, by simp, mem_ML_of_eq [1] (by decide +kernel)⟩)
  have h2 := card_ML_le
  simp only [List.length_cons, List.length_nil] at h
  rw [GP]
  omega

theorem card_GM_le : Nat.card GM ≤ 2160 := by
  have h := card_closure_le_of_cosets ML {gAdd, gSq, gInv, gMF} [1, gMF] (by simp) (by
    intro r hr g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hr with rfl | rfl <;> rcases hg with rfl | rfl | rfl | rfl
    · exact ⟨1, by simp, mem_ML_of_eq [0] (by decide +kernel)⟩
    · exact ⟨1, by simp, mem_ML_of_eq [1] (by decide +kernel)⟩
    · exact ⟨1, by simp, mem_ML_of_eq [2] (by decide +kernel)⟩
    · exact ⟨gMF, by simp, mem_ML_of_eq [] (by decide +kernel)⟩
    · exact ⟨gMF, by simp, mem_ML_of_eq [0, 1, 1, 1, 0, 1] (by decide +kernel)⟩
    · exact ⟨gMF, by simp, mem_ML_of_eq [1, 1, 1] (by decide +kernel)⟩
    · exact ⟨gMF, by simp, mem_ML_of_eq [1, 2] (by decide +kernel)⟩
    · exact ⟨1, by simp, mem_ML_of_eq [1, 1] (by decide +kernel)⟩)
  have h2 := card_ML_le
  simp only [List.length_cons, List.length_nil] at h
  rw [GM]
  omega

theorem card_GA_le : Nat.card GA ≤ 4320 := by
  have h := card_closure_le_of_cosets ML {gAdd, gSq, gInv, gMul, gFrob}
    [1, gMul, gFrob, gMul * gFrob] (by simp) (by
    intro r hr g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hr with rfl | rfl | rfl | rfl <;> rcases hg with rfl | rfl | rfl | rfl | rfl
    · exact ⟨1, by simp, mem_ML_of_eq [0] (by decide +kernel)⟩
    · exact ⟨1, by simp, mem_ML_of_eq [1] (by decide +kernel)⟩
    · exact ⟨1, by simp, mem_ML_of_eq [2] (by decide +kernel)⟩
    · exact ⟨gMul, by simp, mem_ML_of_eq [] (by decide +kernel)⟩
    · exact ⟨gFrob, by simp, mem_ML_of_eq [] (by decide +kernel)⟩
    · exact ⟨gMul, by simp, mem_ML_of_eq [0, 1, 0, 0, 1, 1, 1] (by decide +kernel)⟩
    · exact ⟨gMul, by simp, mem_ML_of_eq [1] (by decide +kernel)⟩
    · exact ⟨gMul, by simp, mem_ML_of_eq [1, 2] (by decide +kernel)⟩
    · exact ⟨1, by simp, mem_ML_of_eq [1] (by decide +kernel)⟩
    · exact ⟨gMul * gFrob, by simp, mem_ML_of_eq [] (by decide +kernel)⟩
    · exact ⟨gFrob, by simp, mem_ML_of_eq [1, 1, 0, 0, 1, 1] (by decide +kernel)⟩
    · exact ⟨gFrob, by simp, mem_ML_of_eq [1, 1, 1] (by decide +kernel)⟩
    · exact ⟨gFrob, by simp, mem_ML_of_eq [2] (by decide +kernel)⟩
    · exact ⟨gMul * gFrob, by simp, mem_ML_of_eq [1] (by decide +kernel)⟩
    · exact ⟨1, by simp, mem_ML_of_eq [] (by decide +kernel)⟩
    · exact ⟨gMul * gFrob, by simp, mem_ML_of_eq [0, 1, 1, 1, 0, 1] (by decide +kernel)⟩
    · exact ⟨gMul * gFrob, by simp, mem_ML_of_eq [1, 1, 1] (by decide +kernel)⟩
    · exact ⟨gMul * gFrob, by simp, mem_ML_of_eq [1, 2] (by decide +kernel)⟩
    · exact ⟨gFrob, by simp, mem_ML_of_eq [1, 1] (by decide +kernel)⟩
    · exact ⟨gMul, by simp, mem_ML_of_eq [] (by decide +kernel)⟩)
  have h2 := card_ML_le
  simp only [List.length_cons, List.length_nil] at h
  rw [GA]
  omega

end CFSG.LocalAnalysis.WeakClosure81.NF3C
