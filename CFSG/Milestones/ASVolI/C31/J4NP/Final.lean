module

public import CFSG.Milestones.ASVolI.C31.J4NP.Tree
public import CFSG.Milestones.ASVolI.C31.J4NP.Top
public import CFSG.Milestones.ASVolI.C31.J4NP.VerdictJNodes
public import CFSG.Milestones.ASVolI.C31.J4NP.M4Type
public import Certificates.Certificate7954

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.J4Tree.Native

section Cover


theorem burnsideJ4NP_ids_cover {k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ treeN) :
    k ∈ burnsideJ4NP_colIds ∨ k ∈ burnsideJ4NP_vjNodeIds ∨ k ∈ burnsideJ4NP_m4Ids := by
  have h := Certificates.certificate7954
  have hN : treeN = 1327 := rfl
  have hvj : burnsideJ4NP_vjNodeIds = burnsideJ4NP_vjIdsLit := rfl
  have hm4 : burnsideJ4NP_m4Ids = burnsideJ4NP_m4IdsLit := rfl
  have hcol : burnsideJ4NP_colIds = CFSG.J4Tree.Native.Col.colNodes.map
      CFSG.J4Tree.Native.Col.VNode.k := rfl
  unfold burnsideJ4NP_idsCoverOK burnsideJ4NP_idsCoverWith at h
  rw [List.all_eq_true] at h
  have hk := h k (List.mem_range'_1.mpr ⟨hk1, by omega⟩)
  simp only [Bool.or_eq_true, List.contains_iff_mem] at hk
  rw [hvj, hm4, hcol]
  rcases hk with (hk | hk) | hk
  · exact Or.inl hk
  · exact Or.inr (Or.inl hk)
  · exact Or.inr (Or.inr hk)

end Cover

section Final


theorem burnsideJ4NP_verdictWH_all (htop : burnsideJ4NP_TopFacts) :
    ∀ k, 1 ≤ k → k ≤ treeN → burnsideJ4NP_VerdictWH (burnsideJ4NP_Wv k) := by
  intro k hk1 hkN
  rcases burnsideJ4NP_ids_cover hk1 hkN with h | h | h
  · exact burnsideJ4NP_verdictWH_colIds k h
  · exact burnsideJ4NP_verdictWH_of_mem_vjNodeIds k h
  · exact burnsideJ4NP_verdictWH_m4Ids
      (burnsideJ4NP_card_centralizer_Rep htop (k := 539) (by norm_num) (by decide) (by decide)) k h

theorem burnsideJ4NP_openReachP : burnsideJ4NP_OpenReachP :=
  burnsideJ4NP_openReachP_of_tree burnsideJ4NP_topFacts
    (burnsideJ4NP_verdictWH_all burnsideJ4NP_topFacts)

end Final

end CFSG.ASVolI
