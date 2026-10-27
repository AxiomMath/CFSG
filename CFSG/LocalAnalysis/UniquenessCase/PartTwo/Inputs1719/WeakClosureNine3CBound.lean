module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNine3CModel

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NF3C

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts Subgroup

theorem mlGen_codes : [ι46 gAdd, ι46 gSq, ι46 gInv].map (codeN 46) = mlGenC := by
  decide +kernel

theorem ml_tbl : Core.tblCheckC (List.range 46) mlGenC mlLit mlTbl = true := by
  decide +kernel

theorem ml_one : List.range 46 ∈ mlLit := by decide +kernel

theorem ml_length : mlLit.length = 1080 := by decide +kernel

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
