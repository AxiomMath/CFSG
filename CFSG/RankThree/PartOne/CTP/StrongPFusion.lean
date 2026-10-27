module

public import CFSG.RankThree.PartOne.CTP.StrongPGlue

public section

namespace CFSG.RankThree.PartOne

open StrongP

section Fusion

variable {H : Type*} [Group H] {p : ℕ} {Y : Subgroup H}

theorem IsStronglyPEmbedded.mem_of_fusion [Fact p.Prime] (hY : IsStronglyPEmbedded p Y)
    {E : Subgroup H} (hEp : IsPGroup p E) (hEY : E ≤ Y) {e g : H} (he : e ∈ E) (he1 : e ≠ 1)
    (hge : g * e * g⁻¹ ∈ E) : g ∈ Y := by
  have hginv : g⁻¹ ∈ Y := by
    by_contra hg
    refine hY.2.2 g⁻¹ hg ?_
    have hord : p ∣ orderOf e := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hEp ⟨e, he⟩
      have hk' : orderOf e = p ^ k := by rw [← Subgroup.orderOf_mk e he]; exact hk
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · rw [h0, pow_zero] at hk'
        exact absurd (orderOf_eq_one_iff.mp hk') he1
      · rw [hk']; exact dvd_pow_self p hpos.ne'
    have hle : Subgroup.zpowers e ≤ Y ⊓ conjSub g⁻¹ Y := by
      refine Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hEY he, ?_⟩)
      rw [mem_conjSub_iff]
      simpa [mul_assoc] using hEY hge
    exact (Nat.card_zpowers e ▸ hord).trans (Subgroup.card_dvd_of_le hle)
  simpa using Y.inv_mem hginv

variable [Finite H]

theorem IsStronglyPEmbedded.false_of_fusion_generation [Fact p.Prime]
    (hY : IsStronglyPEmbedded p Y) (S : Subgroup H) [S.Normal] {E : Subgroup H} (hES : E ≤ S)
    (hEp : IsPGroup p E) (hE1 : E ≠ ⊥) {Γ : Set H} (hΓS : S ≤ Subgroup.closure Γ)
    (hΓ : ∀ g ∈ Γ, ∃ e ∈ E, e ≠ 1 ∧ g * e * g⁻¹ ∈ E) : False := by
  obtain ⟨P', hEP'⟩ := hEp.exists_le_sylow
  have hP' : IsSylowOf p (P' : Subgroup H) ⊤ :=
    ⟨le_top, P'.isPGroup', by simpa [Subgroup.relIndex_top_right] using P'.not_dvd_index⟩
  obtain ⟨c, hc⟩ := hY.exists_conj_ge hP'
  have hY' : IsStronglyPEmbedded p (conjSub c Y) := hY.conj c
  have hEY : E ≤ conjSub c Y := hEP'.trans hc
  have hΓY : Subgroup.closure Γ ≤ conjSub c Y := by
    rw [Subgroup.closure_le]
    intro g hg
    obtain ⟨e, he, he1, hge⟩ := hΓ g hg
    exact hY'.mem_of_fusion hEp hEY he he1 hge
  have hSY : S ≤ conjSub c Y := hΓS.trans hΓY
  have hpS : p ∣ Nat.card S := by
    obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hE1
    have hord : p ∣ orderOf (x : H) := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hEp x
      have hk' : orderOf (x : H) = p ^ k := by rw [Subgroup.orderOf_coe]; exact hk
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · rw [h0, pow_zero] at hk'
        exact absurd (Subtype.ext (orderOf_eq_one_iff.mp hk')) hx1
      · rw [hk']; exact dvd_pow_self p hpos.ne'
    have hxS : (x : H) ∈ S := hES x.2
    have h1 : orderOf (⟨x, hxS⟩ : S) ∣ Nat.card S := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact hord.trans h1
  exact hY'.not_dvd_card_of_normal_le hSY hpS

end Fusion

end CFSG.RankThree.PartOne
