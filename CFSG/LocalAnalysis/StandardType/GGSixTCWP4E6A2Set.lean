module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E6Form
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UE6Disc

public section

namespace CFSG.StandardType.TableCRes

open CFSG.StandardType.KGCentE6 (iform_comm_E6 iform_add_left_E6 iform_smul_left_E6
  iform_sub_left_E6 iform_right_neg_E6)

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

theorem a2Set_eq_of_mem {α β α' β' : Fin Tag.E6.rank → ℤ}
    (hα : IsRoot .E6 α) (hβ : IsRoot .E6 β) (hab : iform α β = -1)
    (h1 : α' ∈ tcA2Set α β) (h2 : β' ∈ tcA2Set α β) (h' : iform α' β' = -1) :
    tcA2Set α' β' = tcA2Set α β := by
  have n1 : iform α α = 2 := e6_iform_self α (mem_rootFinset.2 hα)
  have n2 : iform β β = 2 := e6_iform_self β (mem_rootFinset.2 hβ)
  have hba : iform β α = -1 := by rw [iform_comm_E6]; exact hab
  simp only [tcA2Set, Set.mem_insert_iff, Set.mem_singleton_iff] at h1 h2
  rcases h1 with h1 | h1 | h1 | h1 | h1 | h1 <;>
    rcases h2 with h2 | h2 | h2 | h2 | h2 | h2 <;>
    rw [h1, h2] at h' ⊢ <;>
    first
    | (exfalso
       simp only [iform_add_left_E6, iform_add_right_E6, iform_neg_left_E6,
         iform_right_neg_E6, n1, n2, hab, hba] at h' <;> omega)
    | (ext x
       simp only [tcA2Set, Set.mem_insert_iff, Set.mem_singleton_iff]
       constructor <;> intro h <;> rcases h with h | h | h | h | h | h <;> rw [h] <;>
         first
         | (left; abel1)
         | (right; left; abel1)
         | (right; right; left; abel1)
         | (right; right; right; left; abel1)
         | (right; right; right; right; left; abel1)
         | (right; right; right; right; right; abel1))

theorem tcE6_canon_exists {α β : Fin Tag.E6.rank → ℤ}
    (hα : IsRoot .E6 α) (hβ : IsRoot .E6 β) (hab : iform α β = -1) :
    ∃ p ∈ e6CanonBases, tcA2Set (tcOfL p.1) (tcOfL p.2) = tcA2Set α β := by
  have hA : List.ofFn α ∈ e6RootList := mem_e6RootList_of_isRoot hα
  have hB : List.ofFn β ∈ e6RootList := mem_e6RootList_of_isRoot hβ
  have hip : e6ip (List.ofFn α) (List.ofFn β) = -1 := (iform_eq_e6ip α β).symm.trans hab
  obtain ⟨p, hp, h1, h2⟩ := e6_canon_cover _ hA _ hB hip
  obtain ⟨hl1, hl2⟩ := e6_canon_length p hp
  obtain ⟨-, -, hr3⟩ := e6_canon_roots p hp
  refine ⟨p, hp, ?_⟩
  have q1 : List.ofFn (tcOfL p.1) = p.1 := ofFn_ofL hl1
  have q2 : List.ofFn (tcOfL p.2) = p.2 := ofFn_ofL hl2
  have m1 : tcOfL p.1 ∈ tcA2Set α β := by
    rw [mem_tcA2Set_iff, q1]
    exact h1
  have m2 : tcOfL p.2 ∈ tcA2Set α β := by
    rw [mem_tcA2Set_iff, q2]
    exact h2
  have hi : iform (tcOfL p.1) (tcOfL p.2) = -1 := by
    rw [iform_eq_e6ip, q1, q2]
    exact hr3
  exact a2Set_eq_of_mem hα hβ hab m1 m2 hi

end CFSG.StandardType.TableCRes

end
