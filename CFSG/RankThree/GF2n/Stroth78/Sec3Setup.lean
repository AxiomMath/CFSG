module

public import CFSG.RankThree.GF2n.Stroth78.Reduction
public import CFSG.RankThree.GF2n.Stroth78.Sec2Defs

import CFSG.RankThree.GF2n.Stroth78.Sec2FourteenNonContain
import CFSG.RankThree.GF2n.Stroth78.Sec2Fifteen
import CFSG.RankThree.GF2n.Stroth78.Sec2Six
import CFSG.RankThree.GF2n.Stroth78.Sec2EighteenR

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

structure Sec3Hyp (S : Setting z E F) (a : G) (w : ℕ) : Prop where
  card_F : Nat.card F = 2 ^ (2 * w + 1)
  three_le : 3 ≤ w
  not_caseI : ¬ StrothCaseI z
  assumption212 : Stroth78Assumption212 z
  mem_Q : a ∈ Q z
  not_mem_ZQ : a ∉ ZQ z
  isConj : IsConj z a
  mem_Qa : z ∈ QaOf a

theorem Rbar_le_Lbar (S : Setting z E F) (a : G) : Rbar S a ≤ Lbar S a := by
  have hle : Ra S a ≤ La S a := by
    rw [Ra, La]
    exact sup_le_sup_left (inf_le_inf_right (H z) inf_le_left) (Q z)
  rw [Rbar, Lbar]
  exact Subgroup.map_mono (Subgroup.subgroupOf_mono (H z) hle)

theorem Sec3Hyp.centerIn_Qa_not_le_Q {S : Setting z E F} {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) : ¬ centerIn (QaOf a) ≤ Q z :=
  _root_.CFSG.RankThree.GF2n.Stroth78.centerIn_Qa_not_le_Q S h.mem_Q h.isConj
    h.not_mem_ZQ h.mem_Qa h.assumption212

theorem Sec3Hyp.Rbar_ne_bot {S : Setting z E F} {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) : Rbar S a ≠ ⊥ := by
  obtain ⟨s, hsZ, hsQ⟩ := Set.not_subset.mp h.centerIn_Qa_not_le_Q
  have hsH : s ∈ H z := centerIn_QaOf_le_H S h.mem_Qa hsZ
  let x : ↥(H z) := ⟨s, hsH⟩
  have hx : x ∈ (centerIn (QaOf a) ⊓ H z).subgroupOf (H z) :=
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hsZ, hsH⟩)
  let r : Hbar z := QuotientGroup.mk x
  have hr : r ∈ Rbar S a := by
    rw [← map_R0_eq_Rbar S a]
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  have hr1 : r ≠ 1 := by
    intro h1
    apply hsQ
    have hxq : x ∈ (Q z).subgroupOf (H z) := (QuotientGroup.eq_one_iff x).mp h1
    exact Subgroup.mem_subgroupOf.mp hxq
  refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨r, hr⟩, ?_⟩
  exact fun h1 => hr1 (Subtype.ext_iff.mp h1)

theorem Sec3Hyp.mem_Tset_of_mem_Rbar {S : Setting z E F} {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) {r : Hbar z} (hr : r ∈ Rbar S a) (hr1 : r ≠ 1) :
    r ∈ Tset S a :=
  ⟨Rbar_le_Lbar S a hr, hr1,
    isA2Hbar_of_mem_Rbar S h.mem_Q h.isConj h.not_mem_ZQ h.mem_Qa
      h.centerIn_Qa_not_le_Q r hr hr1⟩

theorem Sec3Hyp.Tset_nonempty {S : Setting z E F} {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) : (Tset S a).Nonempty := by
  obtain ⟨r, hr1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.Rbar_ne_bot
  exact ⟨r, h.mem_Tset_of_mem_Rbar r.2 (by simpa using hr1)⟩

theorem Sec3Hyp.Rbar_le_Xsub {S : Setting z E F} {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) : Rbar S a ≤ Xsub S a := by
  intro r hr
  by_cases hr1 : r = 1
  · rw [hr1]
    exact (Xsub S a).one_mem
  · exact subset_Xsub S a (Tset_subset_Eset S a (h.mem_Tset_of_mem_Rbar hr hr1))

theorem Rbar_isPGroup (S : Setting z E F) {a : G} (hconj : IsConj z a) :
    IsPGroup 2 (Rbar S a) := by
  have hQ : IsPGroup 2 (Q z) := Q_isPGroup S
  have hK : IsPGroup 2 ↥(centerIn (QaOf a) ⊓ H z) :=
    (QaOf_isPGroup S hconj).to_le
      (show centerIn (QaOf a) ⊓ H z ≤ QaOf a from inf_le_left.trans inf_le_left)
  have hnorm : centerIn (QaOf a) ⊓ H z ≤ Subgroup.normalizer (Q z) :=
    inf_le_right.trans (Subgroup.le_normalizer_of_normal_subgroupOf (Q_le_H S))
  have hRa : IsPGroup 2 (Ra S a) :=
    IsPGroup.to_sup_of_normal_left' hQ hK hnorm
  rw [Rbar]
  exact hRa.comap_subtype.map (QuotientGroup.mk' ((Q z).subgroupOf (H z)))

theorem Sec3Hyp.two_pow_le_card_Lbar {S : Setting z E F} {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) : 2 ^ w ≤ Nat.card (Lbar S a) := by
  obtain ⟨r, hr⟩ := (Rbar_isPGroup S h.isConj).exists_card_eq
  have h2 : 2 ≤ Nat.card (Rbar S a) := by
    have h1 : 1 < Nat.card (Rbar S a) :=
      (Subgroup.one_lt_card_iff_ne_bot (Rbar S a)).mpr h.Rbar_ne_bot
    omega
  have hrpos : 1 ≤ r := by
    by_contra hlt
    have h0 : r = 0 := by omega
    rw [h0, pow_zero] at hr
    omega
  have hle : 2 ^ w ≤ 2 ^ (r + w - 1) := by
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  exact hle.trans (card_Lbar_ge_of_width_r S h.isConj h.mem_Q h.not_mem_ZQ h.mem_Qa
    h.card_F hr)

theorem Sec3Hyp.four_lt_card_Lbar {S : Setting z E F} {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) : 4 < Nat.card (Lbar S a) := by
  have h8 : 4 < 2 ^ w := by
    have hle : 2 ^ 3 ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) h.three_le
    norm_num at hle
    omega
  exact h8.trans_le h.two_pow_le_card_Lbar

end CFSG.RankThree.GF2n.Stroth78
