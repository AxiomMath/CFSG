module

public import CFSG.Quasithin.H13.J4Cover

public noncomputable section

namespace CFSG.Quasithin.H13.J4

theorem isSimpleGroup_CmodZ
    : IsSimpleGroup (CQ ⧸ ZC) := by
  obtain ⟨-, -, hsimple⟩ := CFSG.Sporadic.Mathieu.fam_m22_simplicity
  exact MulEquiv.isSimpleGroup m22EquivC.symm

theorem not_isPGroup_CmodZ
    : ¬ IsPGroup 2 (CQ ⧸ ZC) := by
  intro h
  have : Finite (CQ ⧸ ZC) := Nat.finite_of_card_ne_zero (by rw [card_CmodZ]; norm_num)
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).1 h
  rw [card_CmodZ] at hn
  have h3 : (3 : ℕ) ∣ 2 ^ n := hn ▸ (by norm_num : (3 : ℕ) ∣ 443520)
  exact absurd ((Nat.Prime.dvd_of_dvd_pow (by norm_num) h3)) (by norm_num)

theorem pCore_QW
    : CFSG.pCore 2 QW = ⊥ := by
  set D := CFSG.pCore 2 QW with hD
  have hDn : D.Normal := CFSG.pCore_normal
  have hDp : IsPGroup 2 D := CFSG.pCore_isPGroup
  let E : Subgroup CQ := D.subgroupOf CQ
  have hEn : E.Normal := hDn.subgroupOf CQ
  have hEp : IsPGroup 2 E := by
    intro g
    obtain ⟨k, hk⟩ := hDp ⟨((g : CQ) : QW), g.2⟩
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
  have hEZ : E ≤ ZC := by
    have : (E.map (QuotientGroup.mk' ZC)).Normal := hEn.map _ (QuotientGroup.mk'_surjective ZC)
    have hmap := isSimpleGroup_CmodZ.eq_bot_or_eq_top_of_normal (E.map (QuotientGroup.mk' ZC))
    rcases hmap with h | h
    · intro c hc
      have : QuotientGroup.mk' ZC c ∈ E.map (QuotientGroup.mk' ZC) := ⟨c, hc, rfl⟩
      rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
      exact this
    · exfalso
      apply not_isPGroup_CmodZ
      have hp : IsPGroup 2 (E.map (QuotientGroup.mk' ZC)) := hEp.map _
      rw [h] at hp
      exact hp.of_equiv Subgroup.topEquiv
  have hE : E = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    rw [Subgroup.mem_bot]
    obtain ⟨k, hk⟩ := hEp ⟨c, hc⟩
    exact pow_eq_one_of_mem_ZC (hEZ hc) (congrArg Subtype.val hk) (fun h3 =>
      absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num) h3) (by norm_num))
  have hDC : D ⊓ CQ = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hgD, hgC⟩
    have : (⟨g, hgC⟩ : CQ) ∈ E := hgD
    rw [hE, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  have hcomm : ⁅D, CQ⁆ = ⊥ := by
    rw [eq_bot_iff, ← hDC]
    exact Subgroup.commutator_le_inf D CQ
  rw [eq_bot_iff, ← hDC]
  intro g hg
  refine ⟨hg, mem_CQ_iff.2 ?_⟩
  have h := Subgroup.commutator_mem_commutator hg (Zq_le_CQ (Subgroup.mem_zpowers zq))
  rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
  exact h

theorem pCore_W
    : CFSG.pCore 2 W = P.subgroupOf W := by
  apply le_antisymm
  · have hn : (CFSG.pCore 2 W).Normal := CFSG.pCore_normal
    have hp : IsPGroup 2 (CFSG.pCore 2 W) := CFSG.pCore_isPGroup
    have himage : (CFSG.pCore 2 W).map (QuotientGroup.mk' (P.subgroupOf W)) ≤
        CFSG.pCore 2 QW :=
      le_sSup ⟨hn.map _ (QuotientGroup.mk'_surjective _), hp.map _⟩
    rw [pCore_QW] at himage
    intro w hw
    have : QuotientGroup.mk' (P.subgroupOf W) w ∈
        (CFSG.pCore 2 W).map (QuotientGroup.mk' (P.subgroupOf W)) := ⟨w, hw, rfl⟩
    have h2 := himage this
    rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    exact h2
  · refine le_sSup ⟨P_normal, ?_⟩
    have hcard : Nat.card (P.subgroupOf W) = 2 ^ 13 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe P_le_W).toEquiv, card_P]
    exact IsPGroup.of_card hcard

end CFSG.Quasithin.H13.J4
