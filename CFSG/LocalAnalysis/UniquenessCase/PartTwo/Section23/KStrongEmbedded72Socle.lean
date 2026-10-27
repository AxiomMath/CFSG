module

public import CFSG.Fischer.Aut.Complete

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Fischer (innerAut innerAut_normal innerAutEquiv mulAutConj_injective mul_conj_mul_inv
  mem_innerAut)

theorem eq_inner_of_normal_simple_subgroup_mulAut {S : Type} [Group S] [Finite S]
    [IsSimpleGroup S] (hnab : ∃ a b : S, a * b ≠ b * a)
    {K : Subgroup (MulAut S)} (hKn : K.Normal) (hKs : IsSimpleGroup ↥K) :
    K = (MulAut.conj : S →* MulAut S).range := by
  classical
  change K = innerAut S
  have hZ : Subgroup.center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have hamem : a ∈ Subgroup.center S := by
        rw [h]
        exact Subgroup.mem_top a
      exact hab ((Subgroup.mem_center_iff.mp hamem b).symm)
  have hKnormal : K.Normal := hKn
  have hInormal : (innerAut S).Normal := innerAut_normal
  haveI := hKnormal
  haveI := hInormal
  have hKsimple : IsSimpleGroup ↥K := hKs
  haveI := hKsimple
  have hIsimple : IsSimpleGroup ↥(innerAut S) := (innerAutEquiv hZ).symm.isSimpleGroup
  haveI := hIsimple
  have hIne : innerAut S ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot _).mp inferInstance
  have hKI_normal : ((K ⊓ innerAut S).subgroupOf (innerAut S)).Normal :=
    (Subgroup.normal_inf_normal K (innerAut S)).subgroupOf (innerAut S)
  haveI := hKI_normal
  have hcases : K ⊓ innerAut S = ⊥ ∨ innerAut S ≤ K := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((K ⊓ innerAut S).subgroupOf (innerAut S)) with hbot | htop
    · left
      have hdisj : Disjoint (K ⊓ innerAut S) (innerAut S) :=
        Subgroup.subgroupOf_eq_bot.mp hbot
      have h := disjoint_iff.mp hdisj
      rwa [inf_eq_left.mpr inf_le_right] at h
    · right
      have hle : innerAut S ≤ K ⊓ innerAut S := Subgroup.subgroupOf_eq_top.mp htop
      exact hle.trans inf_le_left
  rcases hcases with hbot | hIK
  ·
    exfalso
    have hdisj : Disjoint K (innerAut S) := disjoint_iff.mpr hbot
    have hKtriv : ∀ k ∈ K, k = 1 := by
      intro k hk
      ext g
      have hmem : MulAut.conj g ∈ innerAut S := mem_innerAut.mpr ⟨g, rfl⟩
      have hcomm : Commute k (MulAut.conj g) :=
        Subgroup.commute_of_normal_of_disjoint K (innerAut S) hKn hInormal hdisj
          k (MulAut.conj g) hk hmem
      have hconj : MulAut.conj (k g) = MulAut.conj g := by
        rw [← mul_conj_mul_inv k g]
        rw [show k * MulAut.conj g = MulAut.conj g * k from hcomm]
        rw [mul_assoc, mul_inv_cancel, mul_one]
      simpa using mulAutConj_injective hZ hconj
    have hKbot : K = ⊥ := by
      rw [eq_bot_iff]
      intro k hk
      simpa using hKtriv k hk
    exact (Subgroup.nontrivial_iff_ne_bot K).mp inferInstance hKbot
  ·
    have hI_normal : ((innerAut S).subgroupOf K).Normal := hInormal.subgroupOf K
    haveI := hI_normal
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((innerAut S).subgroupOf K) with hbot | htop
    · exfalso
      have hdisj : Disjoint (innerAut S) K := Subgroup.subgroupOf_eq_bot.mp hbot
      have hIbot : innerAut S = ⊥ := by
        have h := disjoint_iff.mp hdisj
        rwa [inf_eq_left.mpr hIK] at h
      exact hIne hIbot
    · have hKI : K ≤ innerAut S := Subgroup.subgroupOf_eq_top.mp htop
      exact le_antisymm hKI hIK

end CFSG.LocalAnalysis.UniquenessCase.UC22
