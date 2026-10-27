module

public import CFSG.RankThree.GF2n.Stroth80.Sec10Four

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem comm_Lx_Lx_mem_Q {t w : G} (hw : w ∈ Z) {Y Y' : Subgroup G} (hs : Sit M Q Z Y t)
    (hs' : Sit M Q Z Y' (t * w)) (hb : QB Y ⊓ QB Y' ≤ Q) :
    ∀ a ∈ QB Y ⊓ M, ∀ b ∈ QB Y' ⊓ M, ⁅a, b⁆ ∈ Q := by
  intro a ha b hb'
  obtain ⟨haQB, -⟩ := Subgroup.mem_inf.mp ha
  obtain ⟨hbQB, -⟩ := Subgroup.mem_inf.mp hb'
  have hbCZ : b ∈ Subgroup.centralizer (Z : Set G) :=
    (Subgroup.mem_inf.mp (Lx_le_H0 hs' (smith_1_12 hs') hb')).2
  have haCZ : a ∈ Subgroup.centralizer (Z : Set G) :=
    (Subgroup.mem_inf.mp (Lx_le_H0 hs (smith_1_12 hs) ha)).2
  have hbw : Commute b w := (Subgroup.mem_centralizer_iff.mp hbCZ w hw).symm
  have haw : Commute a w := (Subgroup.mem_centralizer_iff.mp haCZ w hw).symm
  have hbtw : Commute b (t * w) := (hs'.QB_comm_X hs'.mem hbQB).symm
  have hat : Commute a t := (hs.QB_comm_X hs.mem haQB).symm
  have hatw : Commute a (t * w) := hat.mul_right haw
  have hbt : Commute b t := by
    have h := hbtw.mul_right hbw.inv_right
    rwa [mul_inv_cancel_right] at h
  have htw1 : t * w ≠ 1 := by
    intro h
    apply hs.notQ
    have hwQ : w ∈ Q := hs.hyp.Z_normal.1 hw
    have e : t = (t * w) * w⁻¹ := by group
    rw [e, h]
    simpa using Q.inv_mem hwQ
  have hbN : b ∈ Subgroup.normalizer (Y : Set G) :=
    Tim77.mem_normalizer_of_commute_of_isTI hs.X_isTI hs.mem hs.ne_one hbt.eq
  have haN : a ∈ Subgroup.normalizer (Y' : Set G) :=
    Tim77.mem_normalizer_of_commute_of_isTI hs'.X_isTI hs'.mem htw1 hatw.eq
  have h1 : b * a⁻¹ * b⁻¹ ∈ QB Y := hs.normalizer_QB hbN ((QB Y).inv_mem haQB)
  have h2 : a * b * a⁻¹ ∈ QB Y' := hs'.normalizer_QB haN hbQB
  refine hb ⟨?_, ?_⟩
  · rw [show ⁅a, b⁆ = a * (b * a⁻¹ * b⁻¹) by
      rw [commutatorElement_def]; group]
    exact (QB Y).mul_mem haQB h1
  · rw [show ⁅a, b⁆ = (a * b * a⁻¹) * b⁻¹ by rw [commutatorElement_def]]
    exact (QB Y').mul_mem h2 ((QB Y').inv_mem hbQB)

theorem Good103.comm_CN_mem_Q (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t w : G} (hw : w ∈ Z) (htw : Good103 M Q Z B (t * w)) {Y Y' : Subgroup G}
    (hs : Sit M Q Z Y t) (hs' : Sit M Q Z Y' (t * w)) (hb : QB Y ⊓ QB Y' ≤ Q) :
    ∀ s ∈ hc.CN t, ∀ a ∈ QB Y ⊓ M, ⁅s, a⁆ ∈ Q := by
  intro s hsCN a ha
  have haM : a ∈ M := (Subgroup.mem_inf.mp ha).2
  have hwQ : w ∈ Q := hs.hyp.Z_normal.1 hw
  have hCN : hc.CN (t * w) = hc.CN t := Ctx.CN_mul_of_mem_Q hc hwQ
  have hle : hc.CN (t * w) ≤ Q ⊔ (QB Y' ⊓ M) :=
    ((stroth_10_4 h34 h311a hspread) G M Q Z B hc n (t * w) Y' H htw hs'.conj
      hs'.mem).1
  have hsSup : s ∈ (QB Y' ⊓ M) ⊔ Q := by
    rw [sup_comm]
    exact (hCN ▸ hle) hsCN
  have hAB : QB Y' ⊓ M ≤ Subgroup.normalizer (Q : Set G) :=
    (inf_le_right : QB Y' ⊓ M ≤ M).trans hc.hyp.Q_normal.2
  obtain ⟨c, hc', y, hy, hcy⟩ := exists_mul_of_mem_sup_of_le_normalizer hAB hsSup
  have h1 : ⁅y, a⁆ ∈ Q := comm_mem_Q hs.hyp haM hy
  have h2 : c * ⁅y, a⁆ * c⁻¹ ∈ Q := conj_mem_Q hs.hyp hc'.2 h1
  have h3 : ⁅c, a⁆ ∈ Q := by
    rw [← commutatorElement_inv]
    exact Q.inv_mem (comm_Lx_Lx_mem_Q hw hs hs' hb a ha c hc')
  rw [← hcy, commutatorElement_mul_left_eq_conj_mul]
  exact Q.mul_mem h2 h3

theorem Good103.inf_QB_inf_QB_le_CN (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good103 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t) :
    QB B ⊓ QB Y ⊓ M ≤ hc.CN t := by
  have hB : B ≤ QB Y :=
    hc.hyp.le_QB_of_mem_QB hc.conj hs.conj hs.mem hs.ne_one ht.1.2.2.2.1
  have hr : (1 : G) ∈ Rt M (LB M Q B) t :=
    le_Rt (LB M Q B) ht.1.mem_LB (Subgroup.one_mem (LB M Q B))
  have h4 := ((stroth_10_4 h34 h311a hspread) G M Q Z B hc n t Y H ht hs.conj hs.mem).2 1 hr
    (by simpa [conjSubgroup_one] using hB)
  rw [conjSubgroup_one, conjSubgroup_one] at h4
  calc QB B ⊓ QB Y ⊓ M ≤ Q ⊔ (QB B ⊓ QB Y ⊓ M) := le_sup_right
    _ = LB M Q B ⊓ hc.CN t := h4.symm
    _ ≤ hc.CN t := inf_le_right

theorem Good103.commute_of_mem_QB_inf_QB (h34 : Stroth34Statement)
    (h311a : Stroth311aStatement) (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B}
    {n : ℕ} (H : Sec10Hyp hc n) {t w : G} (hw : w ∈ Z) (ht : Good103 M Q Z B t)
    (htw : Good103 M Q Z B (t * w)) {Y Y' : Subgroup G} (hs : Sit M Q Z Y t)
    (hs' : Sit M Q Z Y' (t * w)) (hb : QB Y ⊓ QB Y' ≤ Q) :
    ∀ x ∈ QB B ⊓ QB Y ⊓ M, ∀ a ∈ QB Y ⊓ M, x * a = a * x := by
  intro x hx a ha
  obtain ⟨⟨hxB, hxY⟩, -⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨haY, -⟩ := Subgroup.mem_inf.mp ha
  have hxCN : x ∈ hc.CN t :=
    Good103.inf_QB_inf_QB_le_CN h34 h311a hspread H ht hs hx
  have hxQ : ⁅x, a⁆ ∈ Q :=
    Good103.comm_CN_mem_Q h34 h311a hspread H hw htw hs hs' hb x hxCN a ha
  have hxY' : ⁅x, a⁆ ∈ Y := hs.comm_QB_mem_X hxY haY
  have h1 : ⁅x, a⁆ ∈ Y ⊓ Q := ⟨hxY', hxQ⟩
  rw [hs.X_inf_Q, Subgroup.mem_bot] at h1
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

end CFSG.RankThree.GF2n.Stroth80
