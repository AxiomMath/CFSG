module

public import CFSG.LocalAnalysis.WeakClosure81.EightNineAS
public import CFSG.LocalAnalysis.WeakClosure81.EightTwelveDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsU3)

variable {G : Type} [Group G] [Finite G]

theorem Sit813.sup_eq_AS {V H T A L K : Subgroup G} {i : ℕ} (h5_11 : Asch5_11AS)
    (h5_13 : Asch5_13AS) (h : Sit813 V H T i A L K) : T ⊔ K = H := by
  have hTH : IsSylowIn 2 T H := isSylowIn_of_isCalH h.minCex.hyp.calH h.minCex.hyp.sylow
  have hKH : K ≤ H := h.concl813.sub_L.trans h.concl813.comp.2.2.1
  by_contra hne
  have hlt : T ⊔ K < H := lt_of_le_of_ne (sup_le hTH.le hKH) hne
  obtain ⟨X, hX, hle⟩ := exists_mem_calNIn_of_lt le_sup_left hlt
  rw [MinCex88.calNIn_eq_AS h5_11 h5_13 h.minCex, Set.mem_singleton_iff] at hX
  subst hX
  have hKM : K ≤ normalizer (V : Set G) := (le_sup_right.trans hle).trans inf_le_right
  have hone : (K ⊓ normalizer (V : Set G)).relIndex K = 1 :=
    Subgroup.relIndex_eq_one.mpr (le_inf le_rfl hKM)
  rw [h.concl813.d_index] at hone
  norm_num at hone

end CFSG.LocalAnalysis.WeakClosure81

end
