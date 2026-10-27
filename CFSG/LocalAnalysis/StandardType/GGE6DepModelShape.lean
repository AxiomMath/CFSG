module

public import CFSG.LocalAnalysis.StandardType.GGE6DepModelShapeTab
public import CFSG.LocalAnalysis.StandardType.GGE6DepModelShapeTransport

public section

namespace CFSG.StandardType

namespace E6Dep

private theorem cjGen_mono {X Y : Finset ℕ} (hXY : X ⊆ Y) (h : CjGen X) : CjGen Y :=
  fun I hI hcl hYI => h I hI hcl fun x hx => hYI (hXY hx)

theorem shape_theorem {v : Vec6} (hv5 : v 5 = 0) (hv0 : v ≠ 0) {T : Finset Mat6} {r : Mat6}
    (hT : T ⊆ reflFix v) (hr : r ∈ refl36) (hgen : ConjGenerates refl36 (insert r T)) :
    (norm6 v = 1 ∧ ConjGenerates (reflFix v) T) ∨ norm6 v = 0 := by
  have _ : v ≠ 0 := hv0
  have hfix : reflFix v ⊆ refl36 := fun _ hx => (Finset.mem_filter.mp hx).1
  have htri : norm6 v = 0 ∨ norm6 v = 1 ∨ norm6 v = 2 := by
    have hall : ∀ x : ZMod 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide +kernel
    exact hall (norm6 v)
  rcases htri with h0 | h1 | h2
  · exact Or.inr h0
  · left
    refine ⟨h1, ?_⟩
    obtain ⟨c, hc, hcenv⟩ := exists_cen hv5 h1
    have hzset : zset v = fix1 c := by
      rcases hcenv with hv | hv
      · rw [hv]; rfl
      · rw [hv, zset_neg]; rfl
    have hidxfix : idx (reflFix v) = fix1 c := by rw [idx_reflFix, hzset]
    intro S hS hScl hTS
    by_contra hSne
    have hSrefl : S ⊆ refl36 := fun x hx => hfix (hS hx)
    have hidxS : idx S ⊆ fix1 c := by
      intro x hx
      rw [← hidxfix]
      exact idx_mono hS hx
    have hcl : CjClosed (idx S) := conjClosed_idx hSrefl hScl
    have hne : idx S ≠ fix1 c := by
      intro heq
      apply hSne
      have hii : idx S = idx (reflFix v) := by rw [hidxfix, heq]
      exact idx_injOn hSrefl hfix hii
    have hinsSrefl : insert r S ⊆ refl36 := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxS
      · exact hr
      · exact hSrefl hxS
    have hgenS : ConjGenerates refl36 (insert r S) := by
      intro S' hS' hS'cl hins
      apply hgen S' hS' hS'cl
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxT
      · exact hins (Finset.mem_insert_self _ _)
      · exact hins (Finset.mem_insert_of_mem (hTS hxT))
    obtain ⟨r'', hr''lt, _hrl, hidxins⟩ := idx_insert hr S
    have hCj : CjGen (insert r'' (idx S)) := by
      rw [← hidxins]
      exact cjGen_of_conjGenerates hinsSrefl hgenS
    exact absurd hCj (all_not_gen hc hidxS hcl hne hr''lt)
  · exfalso
    have hins : insert r T ⊆ refl36 := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxT
      · exact hr
      · exact hfix (hT hxT)
    have hCjT : CjGen (idx (insert r T)) := cjGen_of_conjGenerates hins hgen
    obtain ⟨r', hr'lt, _hrl, hidxins⟩ := idx_insert hr T
    have hidxT : idx T ⊆ zset v := by
      intro x hx
      rw [← idx_reflFix v]
      exact idx_mono hT hx
    have hsub : insert r' (idx T) ⊆ insert r' (zset v) := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (hidxT hx)
    have hCjT' : CjGen (insert r' (idx T)) := by
      rw [← hidxins]
      exact hCjT
    exact norm2_not_gen hv5 h2 hr'lt (cjGen_mono hsub hCjT')

end E6Dep

end CFSG.StandardType

end
