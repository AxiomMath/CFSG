module

public import CFSG.Foundations.Basic

public section

namespace CFSG.RankThree.PartOne.KFU

open CFSG

theorem layer_eq_of_normal {M : Type*} [Group M] {K : Subgroup M} (hK : K.Normal)
    (hq : IsQuasisimple K) (hsolv : Group.IsSolvable (M ⧸ K)) : layer M = K := by
  refine le_antisymm (sSup_le fun C hC => ?_) (le_sSup ⟨hq, hK.isSubnormal⟩)
  have hCperf : Group.IsPerfect C := hC.1.1
  have himg : Group.IsPerfect (C.map (QuotientGroup.mk' K)) := Group.IsPerfect.map _
  have hbot : C.map (QuotientGroup.mk' K) = ⊥ := by
    by_contra hne
    have : Nontrivial ↥(C.map (QuotientGroup.mk' K)) :=
      (Subgroup.nontrivial_iff_ne_bot _).2 hne
    exact Group.IsPerfect.not_isSolvable ↥(C.map (QuotientGroup.mk' K)) inferInstance
  intro x hx
  have hx' : QuotientGroup.mk' K x ∈ C.map (QuotientGroup.mk' K) := ⟨x, hx, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hx'
  exact (QuotientGroup.eq_one_iff x).1 hx'

end CFSG.RankThree.PartOne.KFU
