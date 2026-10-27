module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1Cen2A
public import CFSG.LargeExtraspecial.S3Qa
public import CFSG.LargeExtraspecial.BridgeNat
public import Certificates.Certificate21140

public section

namespace CFSG.Sporadic.Co1Patterson

open Subgroup CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier
open scoped commutatorElement

section Closure

variable {G : Type*} [Group G] {s : Set G} {c : G}

theorem mul_comm_of_mem_closure (hc : ∀ x ∈ s, x * c = c * x) {x : G} (hx : x ∈ closure s) :
    x * c = c * x := by
  have hle : closure s ≤ centralizer {c} := by
    rw [closure_le]
    intro y hy
    exact mem_centralizer_singleton_iff.mpr (hc y hy)
  exact mem_centralizer_singleton_iff.mp (hle hx)

theorem mul_comm_of_mem_zpowers (hc : ∀ x ∈ s, x * c = c * x) {x n : G}
    (hx : x ∈ closure s) (hn : n ∈ zpowers c) : x * n = n * x := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hn
  exact ((show Commute x c from mul_comm_of_mem_closure hc hx).zpow_right k).eq

theorem commutator_mem_zpowers_of_mem_closure (hc : ∀ x ∈ s, x * c = c * x)
    (hs : ∀ a ∈ s, ∀ b ∈ s, ⁅a, b⁆ ∈ zpowers c) {x y : G} (hx : x ∈ closure s)
    (hy : y ∈ closure s) : ⁅x, y⁆ ∈ zpowers c := by
  have h1 : ∀ b ∈ s, ∀ x ∈ closure s, ⁅x, b⁆ ∈ zpowers c := by
    intro b hb x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact hs x hx b hb
    | one => simp
    | mul x y hx hy ihx ihy =>
      have e : ⁅x * y, b⁆ = x * ⁅y, b⁆ * x⁻¹ * ⁅x, b⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e, mul_comm_of_mem_zpowers hc hx ihy, mul_inv_cancel_right]
      exact mul_mem ihy ihx
    | inv x hx ihx =>
      have e : ⁅x⁻¹, b⁆ = x⁻¹ * ⁅x, b⁆⁻¹ * x := by
        simp only [commutatorElement_def]
        group
      rw [e, mul_comm_of_mem_zpowers hc (inv_mem hx) (inv_mem ihx), inv_mul_cancel_right]
      exact inv_mem ihx
  induction hy using Subgroup.closure_induction with
  | mem y hy => exact h1 y hy x hx
  | one => simp
  | mul y z hy hz ihy ihz =>
    have e : ⁅x, y * z⁆ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e, mul_comm_of_mem_zpowers hc hy ihz, mul_inv_cancel_right]
    exact mul_mem ihy ihz
  | inv y hy ihy =>
    have e : ⁅x, y⁻¹⁆ = y⁻¹ * ⁅x, y⁆⁻¹ * y := by
      simp only [commutatorElement_def]
      group
    rw [e, mul_comm_of_mem_zpowers hc (inv_mem hy) (inv_mem ihy), inv_mul_cancel_right]
    exact inv_mem ihy

theorem sq_mem_zpowers_of_mem_closure (hc : ∀ x ∈ s, x * c = c * x)
    (hs : ∀ a ∈ s, ∀ b ∈ s, ⁅a, b⁆ ∈ zpowers c) (hsq : ∀ a ∈ s, a ^ 2 ∈ zpowers c) {x : G}
    (hx : x ∈ closure s) : x ^ 2 ∈ zpowers c := by
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hsq x hx
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hn := commutator_mem_zpowers_of_mem_closure hc hs hy hx
    have e : (x * y) ^ 2 = x * ⁅y, x⁆ * x⁻¹ * (x ^ 2 * y ^ 2) := by
      simp only [commutatorElement_def, sq]
      group
    rw [e, mul_comm_of_mem_zpowers hc hx hn, mul_inv_cancel_right]
    exact mul_mem hn (mul_mem ihx ihy)
  | inv x hx ihx =>
    rw [inv_pow]
    exact inv_mem ihx

end Closure

theorem twoAQ_extra_check :
    Native.qExtraOK iotaARows twoAQRows = true :=
  Certificates.certificate21140

theorem twoAQ_extra_parts :
    (∀ q ∈ twoAQRows, Co1Schreier.Native.mul q q = Co1Schreier.Native.one ∨
      Co1Schreier.Native.mul q q = iotaARows) ∧
    ∀ p ∈ twoAQRows, ∀ q ∈ twoAQRows,
      Co1Schreier.Native.mul p q = Co1Schreier.Native.mul q p ∨
        Co1Schreier.Native.mul p q =
          Co1Schreier.Native.mul iotaARows (Co1Schreier.Native.mul q p) := by
  have h := twoAQ_extra_check
  simp only [Native.qExtraOK, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    beq_iff_eq] at h
  exact h

theorem iotaQRows_mem {k : ℕ} (hk : k < 8) : iotaQRows k ∈ twoAQRows :=
  List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩

theorem twoAQ_eq_closure : twoAQ = Subgroup.closure (twoAQg '' {l | l < 8}) := by
  rw [← twoAQRows_length]
  rfl

theorem twoAQg_mem_twoAQ {k : ℕ} (hk : k < 8) : twoAQg k ∈ twoAQ := by
  rw [twoAQ_eq_closure]
  exact subset_closure ⟨k, hk, rfl⟩

theorem twoAQg_sq_mem
    {k : ℕ} (hk : k < 8) :
    twoAQg k ^ 2 ∈ zpowers aG := by
  have hr := (rep_iotaQ k).mul (rep_iotaQ k)
  rw [sq]
  rcases twoAQ_extra_parts.1 _ (iotaQRows_mem hk) with h | h <;> rw [h] at hr
  · have e : twoAQg k * twoAQg k = 1 := hr.eq MRep.one
    rw [e]
    exact one_mem _
  · have e : twoAQg k * twoAQg k = aG := hr.eq rep_iotaA
    rw [e]
    exact mem_zpowers _

theorem twoAQg_commutator_mem
    {i j : ℕ} (hi : i < 8)
    (hj : j < 8) : ⁅twoAQg i, twoAQg j⁆ ∈ zpowers aG := by
  have h1 := (rep_iotaQ i).mul (rep_iotaQ j)
  rcases twoAQ_extra_parts.2 _ (iotaQRows_mem hi) _ (iotaQRows_mem hj) with h | h <;>
    rw [h] at h1
  · have e : twoAQg i * twoAQg j = twoAQg j * twoAQg i := h1.eq ((rep_iotaQ j).mul (rep_iotaQ i))
    rw [(@commutatorElement_eq_one_iff_mul_comm GL24 inferInstance _ _).2 e]
    exact one_mem _
  · have e : twoAQg i * twoAQg j = aG * (twoAQg j * twoAQg i) :=
      h1.eq (rep_iotaA.mul ((rep_iotaQ j).mul (rep_iotaQ i)))
    have e' : ⁅twoAQg i, twoAQg j⁆ = aG := by
      rw [commutatorElement_def, e]
      group
    rw [e']
    exact mem_zpowers _

theorem eq_one_or_eq_aG_of_mem_twoAQ
    {x : GL24} (hx : x ∈ twoAQ)
    (hc : ∀ y ∈ twoAQ, x * y = y * x) : x = 1 ∨ x = aG :=
  CFSG.ComponentClassification.RankTwoSporadic.Co1.eq_one_or_eq_aG_of_comm (twoAQ_le hx)
    fun _ hk => hc _ (twoAQg_mem_twoAQ hk)

theorem mul_aG_comm_of_mem_twoAQ
    {y : GL24} (hy : y ∈ twoAQ) :
    y * aG = aG * y :=
  (@mem_centralizer_singleton_iff GL24 inferInstance aG y).mp (mem_inf.mp (twoAQ_le hy)).2


theorem twoAQ_extraspecial : CFSG.Open.timmesfeldIsExtraspecial (twoAQ : Subgroup GL24) := by
  have hcs : ∀ x ∈ twoAQg '' {l | l < 8}, x * aG = aG * x := by
    rintro _ ⟨k, hk, rfl⟩
    exact twoAQg_comm k hk
  have hss : ∀ a ∈ twoAQg '' {l | l < 8}, ∀ b ∈ twoAQg '' {l | l < 8}, ⁅a, b⁆ ∈ zpowers aG := by
    rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
    exact twoAQg_commutator_mem hi hj
  have hsq : ∀ a ∈ twoAQg '' {l | l < 8}, a ^ 2 ∈ zpowers aG := by
    rintro _ ⟨k, hk, rfl⟩
    exact twoAQg_sq_mem hk
  have hz : ∀ n ∈ zpowers aG, n = 1 ∨ n = aG := by
    intro n hn
    have h := @CFSG.LargeExtraspecial.Setting.mem_zpowers_iff_of_mul_self GL24 inferInstance aG n
      aG_sq
    exact h.mp hn
  have hZ : ∀ x ∈ twoAQ, (∀ y ∈ twoAQ, x * y = y * x) ↔ x = 1 ∨ x = aG := by
    intro x hx
    refine ⟨eq_one_or_eq_aG_of_mem_twoAQ hx, ?_⟩
    rintro (rfl | rfl) y hy
    · simp
    · exact (mul_aG_comm_of_mem_twoAQ hy).symm
  have hp : IsPGroup 2 twoAQ := IsPGroup.of_card (n := 9) (by rw [card_twoAQ]; norm_num)
  have hcomm : ∀ x ∈ twoAQ, ∀ y ∈ twoAQ, x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = aG := by
    intro x hx y hy
    rw [twoAQ_eq_closure] at hx hy
    have h := @commutator_mem_zpowers_of_mem_closure GL24 inferInstance _ aG hcs hss x y hx hy
    exact hz _ h
  have hsq' : ∀ x ∈ twoAQ, x ^ 2 = 1 ∨ x ^ 2 = aG := by
    intro x hx
    rw [twoAQ_eq_closure] at hx
    have h := @sq_mem_zpowers_of_mem_closure GL24 inferInstance _ aG hcs hss hsq x hx
    exact hz _ h
  have hnc : ∃ x ∈ twoAQ, ∃ y ∈ twoAQ, x * y ≠ y * x := by
    by_contra! hall
    have hsub : (twoAQ : Set GL24) ⊆ {1, aG} := fun x hx =>
      (hZ x hx).1 fun y hy => hall x hx y hy
    have h2 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h3 : ({1, aG} : Set GL24).ncard ≤ 2 :=
      (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
    rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe, card_twoAQ] at h2
    omega
  have h := @CFSG.LargeExtraspecial.isExtraspecialPGroup_two_of_center GL24 inferInstance
    inferInstance twoAQ aG hp aG_mem_twoAQ aG_ne_one hZ hcomm hsq' hnc
  exact (CFSG.LargeExtraspecial.Bridge.timmesfeldIsExtraspecial_iff _).2 h

theorem exists_mem_twoAQ_mul_ne : ∃ x ∈ twoAQ, ∃ y ∈ twoAQ, x * y ≠ y * x := by
  have h := twoAQ_extraspecial
  by_contra! hall
  have hc : center (twoAQ : Subgroup GL24) = ⊤ := eq_top_iff.mpr fun x _ =>
    mem_center_iff.mpr fun y => Subtype.ext (hall _ y.2 _ x.2)
  have h2 := h.2.2.2
  rw [hc, card_top, card_twoAQ] at h2
  omega

end CFSG.Sporadic.Co1Patterson
