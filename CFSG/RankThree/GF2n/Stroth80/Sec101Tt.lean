module

public import CFSG.RankThree.GF2n.Stroth80.Sec10Four

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Good101.Vt_le_Tt (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ}
    (H : Sec10Hyp hc n) {t : G} (ht : Good101 M Q Z B t) :
    Vt M (LB M Q B) B Z t ≤ Tt Q Z (Vt M (LB M Q B) B Z t) t := by
  obtain ⟨m, hm, hsl⟩ := SLlike.exists_SLMNat (H.slLike ht)
  exact hc.Vt_le_Tt_of_SLNat (H.toSec5 ht.mem_LB ht.2.2.1)
    (stroth_3_5 h34 hc H.width H.n_gt H.noA2 H.gen).2.1 (SLMNat.toSLNat hsl hm)

theorem Good101.Vt_le_Ut (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ}
    (H : Sec10Hyp hc n) {t : G} (ht : Good101 M Q Z B t) :
    Vt M (LB M Q B) B Z t ≤ Ut Q Z t :=
  (ht.Vt_le_Tt h34 H).trans (sup_le_sup_right (Subgroup.commutator_mono inf_le_left le_rfl) Z)

theorem Good101.comm_not_mem_Tt (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ}
    (H : Sec10Hyp hc n) {t : G} (ht : Good101 M Q Z B t) {c : G} (hcQ : c ∈ Q)
    (hcW : c ∉ Wt Q (Vt M (LB M Q B) B Z t)) :
    ⁅t, c⁆ ∉ Tt Q Z (Vt M (LB M Q B) B Z t) t := by
  intro hx
  apply hcW
  refine (hc.comm_mem_Tt_iff ht.mem_LB (ht.Vt_le_Ut h34 H) hcQ).mp ?_
  rw [← commutatorElement_inv]
  exact (Tt Q Z (Vt M (LB M Q B) B Z t) t).inv_mem hx

theorem Good101.comm_comm_self (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ}
    (H : Sec10Hyp hc n) {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t)
    {c : G} (hcQ : c ∈ Q) : ⁅t, c⁆ * t = t * ⁅t, c⁆ := by
  obtain ⟨m, hm, hsl⟩ := SLlike.exists_SLMNat (H.slLike ht)
  have ht2 : t ^ 2 = 1 := by rw [pow_two]; exact hs.x_sq
  have hU := hc.Ut_le_centralizer h34 (H.toSec5 ht.mem_LB ht.2.2.1) (SLMNat.toSLNat hsl hm) ht2
  have hx : ⁅t, c⁆ ∈ Ut Q Z t := by
    rw [← commutatorElement_inv]
    exact (Ut Q Z t).inv_mem (comm_mem_Ut hcQ)
  exact Subgroup.mem_centralizer_singleton_iff.mp (hU hx)

omit [Finite G] in
theorem conj_eq_mul_comm_of_mul_self {t : G} (ht2 : t * t = 1) (c : G) :
    c * t * c⁻¹ = t * ⁅t, c⁆ := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  calc c * t * c⁻¹ = (t * t) * c * t⁻¹ * c⁻¹ := by rw [ht2, htinv]; group
    _ = t * ⁅t, c⁆ := by simp only [commutatorElement_def]; group

theorem Good101.conj_comm_self (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ}
    (H : Sec10Hyp hc n) {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t)
    {c : G} (hcQ : c ∈ Q) : c * t * c⁻¹ * t = t * (c * t * c⁻¹) := by
  rw [conj_eq_mul_comm_of_mul_self hs.x_sq c, mul_assoc, ht.comm_comm_self h34 H hs hcQ]

private theorem Good101.sup_inf_QB_inf_Vt (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t) :
    Z ⊔ Q ⊓ QB Y ⊓ Vt M (LB M Q B) B Z t = Vt M (LB M Q B) B Z t := by
  set V := Vt M (LB M Q B) B Z t
  have hVle : V ≤ Q ⊓ QB Y ⊔ Z := by
    have h := H.Vt_le (stroth_5_7 h34 hspread) ht
    rwa [inf_QB_zpowers_eq hs] at h
  refine le_antisymm (sup_le sec39_Z_le_Vt inf_le_right) fun v hv => ?_
  have hAN : Q ⊓ QB Y ≤ Subgroup.normalizer (Z : Set G) :=
    fun _ ha => hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 ha.1)
  obtain ⟨a, haA, z, hz, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hAN (hVle hv)
  have haV : a ∈ V := by
    have e : a = a * z * z⁻¹ := by group
    rw [e]
    exact V.mul_mem hv (V.inv_mem (sec39_Z_le_Vt hz))
  exact (Z ⊔ Q ⊓ QB Y ⊓ V).mul_mem (Subgroup.mem_sup_right ⟨haA, haV⟩)
    (Subgroup.mem_sup_left hz)

theorem Good101.card_inf_QB_inf_Vt (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t) {m : ℕ}
    (hm : SLMNat hc t m) : Nat.card ↥(Q ⊓ QB Y ⊓ Vt M (LB M Q B) B Z t) = Nat.card Z ^ m := by
  have hN : Q ⊓ QB Y ⊓ Vt M (LB M Q B) B Z t ≤ Subgroup.normalizer (Z : Set G) :=
    fun _ ha => hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 ha.1.1)
  have hinf : Z ⊓ (Q ⊓ QB Y ⊓ Vt M (LB M Q B) B Z t) = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    have h' : a ∈ Z ⊓ QB Y := ⟨ha.1, ha.2.1.2⟩
    rwa [Z_inf_QB_eq_bot hs (smith_1_12 hs)] at h'
  have hcard := card_sup_mul_card_inf_of_normalizer hN
  rw [ht.sup_inf_QB_inf_Vt h34 hspread H hs, hinf, Subgroup.card_bot, mul_one, hm.card_Vt,
    pow_succ', mul_comm] at hcard
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (hcard.symm.trans (mul_comm _ _))

end CFSG.RankThree.GF2n.Stroth80
