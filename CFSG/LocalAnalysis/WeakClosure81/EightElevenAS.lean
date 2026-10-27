module

public import CFSG.LocalAnalysis.WeakClosure81.EightNineAS
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12b
public import CFSG.LocalAnalysis.WeakClosure81.EightFour

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (W3Lem86_1)

variable {G : Type} [Group G] [Finite G]

theorem MinCex88.le_pCoreOf_AS {V H T : Subgroup G} {i : ℕ} (h861 : W3Lem86_1 G)
    (h5_11 : Asch5_11AS) (h5_13 : Asch5_13AS) (h : MinCex88 V H T i) : V ≤ pCoreOf 2 H := by
  by_contra hVnot
  have hH0 : ¬ IsCalH0 V H := fun h0 => hVnot h0.2
  set W : Subgroup G := E3.wClos V 0 T with hWdef
  have h86 := h861 V H T h.hyp.hyp7 h.hyp.calH hH0 h.hyp.sylow h.hyp.wne
    (Or.inl h.hyp.centr)
  rw [← hWdef] at h86
  have hTH : IsSylowIn 2 T H := isSylowIn_of_isCalH h.hyp.calH h.hyp.sylow
  have hTW : T ≤ Subgroup.normalizer (W : Set G) :=
    Subgroup.le_normalizer.trans (E3.normalizer_le_normalizer_wClos (V := V) (i := 0) T)
  have hTY : T ≤ H ⊓ Subgroup.normalizer (W : Set G) := le_inf hTH.le hTW
  have hlt : H ⊓ Subgroup.normalizer (W : Set G) < H := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro heq
    have hHN : H ≤ Subgroup.normalizer (W : Set G) := heq ▸ inf_le_right
    have hWT : W ≤ T := wClos_zero_le V T
    have hW0P : W ≤ pCoreOf 2 H :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hWT.trans hTH.le) hHN
        (hTH.isPGroup.to_le hWT)
    have hVW : V ≤ W := by
      have hVT : V ≤ T := le_of_isCalH h.hyp.hyp7.1 h.hyp.calH h.hyp.sylow
      have h1 : conjSubgroup V 1 ≤ W := conjSubgroup_le_wClos_zero (by rwa [conjSubgroup_one])
      rwa [conjSubgroup_one] at h1
    exact hVnot (hVW.trans hW0P)
  obtain ⟨X, hX, hYle⟩ := exists_mem_calNIn_of_lt hTY hlt
  rw [MinCex88.calNIn_eq_AS h5_11 h5_13 h, Set.mem_singleton_iff] at hX
  subst hX
  exact h.hyp.notLe (by
    rw [h86.1]
    exact sup_le inf_le_right (hYle.trans inf_le_right))

end CFSG.LocalAnalysis.WeakClosure81

end
