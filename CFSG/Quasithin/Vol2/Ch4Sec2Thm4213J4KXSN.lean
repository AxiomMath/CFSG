module

public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4KXQS
public import CFSG.Open.QuasithinDefs

public section

namespace CFSG.Quasithin.H13.Ch4.J4KX

open CFSG.Open

section Subnormal

variable {G : Type} [Group G]

theorem isSubnormal_inf {K M : Subgroup G} (hK : IsSubnormal K M) (N : Subgroup G) :
    IsSubnormal (K ⊓ N) (M ⊓ N) := by
  induction hK with
  | refl H => exact IsSubnormal.refl _
  | @step H M' K' h1 h2 h3 ih =>
    refine IsSubnormal.step (inf_le_inf_right N h1) ?_ ih
    rw [Subgroup.normal_subgroupOf_iff (inf_le_inf_right N h1)]
    rw [Subgroup.normal_subgroupOf_iff h1] at h2
    intro h g hh hg
    exact Subgroup.mem_inf.mpr ⟨h2 h g hh.1 hg.1, N.mul_mem (N.mul_mem hg.2 hh.2) (N.inv_mem hg.2)⟩

theorem isSubnormal_sandwich {K M N : Subgroup G} (hK : IsSubnormal K M) (hKN : K ≤ N)
    (hNM : N ≤ M) : IsSubnormal K N := by
  have h := isSubnormal_inf hK N
  rwa [inf_eq_left.mpr hKN, inf_eq_right.mpr hNM] at h

theorem eq_or_le_center_of_isSubnormal {Q B : Subgroup G} (hQ : CFSG.IsQuasisimple ↥Q)
    (h : IsSubnormal B Q) :
    B = Q ∨ B ≤ (Subgroup.center ↥Q).map Q.subtype := by
  induction h with
  | refl H => exact Or.inl rfl
  | @step H M K h1 h2 h3 ih =>
    rcases ih hQ with hM | hM
    · have h2' : (H.subgroupOf K).Normal := hM ▸ h2
      haveI := h2'
      have hHK : H ≤ K := hM ▸ h1
      rcases normal_le_center_or_top hQ (H.subgroupOf K) with hc | htop
      · right
        intro x hx
        have hxK : x ∈ K := hHK hx
        have hy : (⟨x, hxK⟩ : ↥K) ∈ H.subgroupOf K := Subgroup.mem_subgroupOf.mpr hx
        exact Subgroup.mem_map.mpr ⟨⟨x, hxK⟩, hc hy, rfl⟩
      · left
        have hKH : K ≤ H := Subgroup.subgroupOf_eq_top.mp htop
        exact le_antisymm hHK hKH
    · right
      exact h1.trans hM

theorem ne_bot_of_isQuasisimple {Q : Subgroup G} (hQ : CFSG.IsQuasisimple ↥Q) : Q ≠ ⊥ := by
  intro hbot
  subst hbot
  obtain ⟨a, b, hab⟩ := hQ.2.2
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  have ha : (a : G) = 1 := Subgroup.mem_bot.mp a.2
  have hb : (b : G) = 1 := Subgroup.mem_bot.mp b.2
  have hab' : a * b = b * a := Subtype.ext (by simp [ha, hb])
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hab']

theorem quasithinIsCComponent_of_normal {X Q : Subgroup G} (hQ : CFSG.IsQuasisimple ↥Q)
    (hQX : Q ≤ X) (hQN : (Q.subgroupOf X).Normal) : quasithinIsCComponent Q X := by
  refine ⟨ne_bot_of_isQuasisimple hQ, Subgroup.isPerfect_iff.mp hQ.1,
    IsSubnormal.step hQX hQN (IsSubnormal.refl X), ?_⟩
  intro K hKQ hK1 hKp hsub
  have hKQ' : K ≤ Q := hKQ.le
  have hsub' : IsSubnormal K Q := isSubnormal_sandwich hsub hKQ' hQX
  rcases eq_or_le_center_of_isSubnormal hQ hsub' with h | h
  · exact hKQ.ne h
  · apply hK1
    have hcomm : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := by
      intro a ha b hb
      obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp (h ha)
      have := Subgroup.mem_center_iff.mp ha' ⟨b, hKQ' hb⟩
      exact congrArg Subtype.val this |>.symm
    have hle : ⁅K, K⁆ ≤ ⊥ := by
      refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
      rw [commutatorElement_def, hcomm a ha b hb]
      simp
    exact hKp.symm.trans (le_bot_iff.mp hle)

end Subnormal

end CFSG.Quasithin.H13.Ch4.J4KX

end
