module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec15.F153L3C2

open scoped commutatorElement

variable {G : Type} [Group G]

theorem quot_pCore_two_eq_bot (Y : Subgroup G) :
    CFSG.pCore 2 (↥Y ⧸ CFSG.pCore 2 ↥Y) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Y) x
  have hM : IsPGroup 2 ((CFSG.pCore 2 (↥Y ⧸ CFSG.pCore 2 ↥Y)).comap
      (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))) :=
    IsPGroup.comap_of_ker_isPGroup
      (CFSG.pCore_isPGroup (p := 2) (G := ↥Y ⧸ CFSG.pCore 2 ↥Y))
      (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))
      (by rw [QuotientGroup.ker_mk']; exact CFSG.pCore_isPGroup)
  have hMle : (CFSG.pCore 2 (↥Y ⧸ CFSG.pCore 2 ↥Y)).comap
      (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) ≤ CFSG.pCore 2 ↥Y :=
    le_sSup ⟨inferInstance, hM⟩
  have hy : y ∈ (CFSG.pCore 2 (↥Y ⧸ CFSG.pCore 2 ↥Y)).comap
      (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) := hx
  exact Subgroup.mem_bot.mpr ((QuotientGroup.eq_one_iff y).mpr (hMle hy))

theorem odd_card_center_of_pCore_eq_bot {Q : Type*} [Group Q] [Finite Q]
    (hO : CFSG.pCore 2 Q = ⊥) : Odd (Nat.card (Subgroup.center Q)) := by
  by_contra hodd
  have h2 : 2 ∣ Nat.card (Subgroup.center Q) :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center Q)) 2 h2
  have hz' : orderOf (z : Q) = 2 := (Subgroup.orderOf_coe z).trans hz
  have hzc : (z : Q) ∈ Subgroup.center Q := z.2
  haveI hnorm : (Subgroup.zpowers (z : Q)).Normal := by
    refine ⟨fun m hm g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hm
    have hc : Commute g (z : Q) := Subgroup.mem_center_iff.mp hzc g
    rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩
  have hP : IsPGroup 2 (Subgroup.zpowers (z : Q)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz', pow_one])
  have hle : Subgroup.zpowers (z : Q) ≤ CFSG.pCore 2 Q := le_sSup ⟨hnorm, hP⟩
  rw [hO] at hle
  have hz1 : (z : Q) = 1 := Subgroup.mem_bot.mp (hle (Subgroup.mem_zpowers _))
  rw [hz1, orderOf_one] at hz'
  norm_num at hz'

theorem odd_card_center_quot [Finite G] (Y : Subgroup G) :
    Odd (Nat.card (Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y))) :=
  odd_card_center_of_pCore_eq_bot (quot_pCore_two_eq_bot Y)

theorem quot_commutator_central_left {Q : Type*} [Group Q] {z : Q}
    (hz : z ∈ Subgroup.center Q) (a y : Q) : ⁅z * a, y⁆ = ⁅a, y⁆ := by
  have hz' := Subgroup.mem_center_iff.1 hz
  simp only [commutatorElement_def, mul_inv_rev]
  have : z * a * y * (a⁻¹ * z⁻¹) * y⁻¹ = z * (a * y * a⁻¹) * z⁻¹ * y⁻¹ := by group
  rw [this, ← hz' (a * y * a⁻¹)]
  group

theorem quot_commutator_central_right {Q : Type*} [Group Q] {w : Q}
    (hw : w ∈ Subgroup.center Q) (x b : Q) : ⁅x, w * b⁆ = ⁅x, b⁆ := by
  have hw' := Subgroup.mem_center_iff.1 hw
  simp only [commutatorElement_def, mul_inv_rev]
  have : x * (w * b) * x⁻¹ * (b⁻¹ * w⁻¹) = w * (x * b * x⁻¹ * b⁻¹) * w⁻¹ := by
    rw [← mul_assoc x w b, hw' x]
    group
  rw [this, ← hw' (x * b * x⁻¹ * b⁻¹)]
  group

theorem quot_commutator_central_mul {Q : Type*} [Group Q] {z w : Q}
    (hz : z ∈ Subgroup.center Q) (hw : w ∈ Subgroup.center Q) (a b : Q) :
    ⁅z * a, w * b⁆ = ⁅a, b⁆ := by
  rw [quot_commutator_central_left hz, quot_commutator_central_right hw]

theorem quasi_normal_le_center_or_eq_top {Q : Type*} [Group Q] (hq : CFSG.IsQuasisimple Q)
    (N : Subgroup Q) [N.Normal] : N ≤ Subgroup.center Q ∨ N = ⊤ := by
  obtain ⟨hperf, hsimp, -⟩ := hq
  haveI : (N.map (QuotientGroup.mk' (Subgroup.center Q))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  rcases hsimp.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' (Subgroup.center Q)))
    with h | h
  · left
    intro x hx
    have hmem : (QuotientGroup.mk' (Subgroup.center Q)) x ∈
        N.map (QuotientGroup.mk' (Subgroup.center Q)) :=
      Subgroup.mem_map_of_mem _ hx
    rw [h, Subgroup.mem_bot] at hmem
    exact (QuotientGroup.eq_one_iff x).mp hmem
  · right
    have key : ∀ q : Q, ∃ z ∈ Subgroup.center Q, ∃ n ∈ N, q = z * n := by
      intro q
      have hq' : (QuotientGroup.mk' (Subgroup.center Q)) q ∈
          N.map (QuotientGroup.mk' (Subgroup.center Q)) := by
        rw [h]
        exact Subgroup.mem_top _
      obtain ⟨n, hn, hnq⟩ := Subgroup.mem_map.mp hq'
      refine ⟨q * n⁻¹, ?_, n, hn, by group⟩
      have h1 : (QuotientGroup.mk' (Subgroup.center Q)) (q * n⁻¹) = 1 := by
        rw [map_mul, map_inv, ← hnq, mul_inv_cancel]
      exact (QuotientGroup.eq_one_iff (N := Subgroup.center Q) (q * n⁻¹)).mp h1
    have hcomm : ∀ a b : Q, ⁅a, b⁆ ∈ N := by
      intro a b
      obtain ⟨z1, hz1, n1, hn1, rfl⟩ := key a
      obtain ⟨z2, hz2, n2, hn2, rfl⟩ := key b
      rw [quot_commutator_central_mul hz1 hz2 n1 n2, commutatorElement_def]
      exact N.mul_mem (N.mul_mem (N.mul_mem hn1 hn2) (N.inv_mem hn1)) (N.inv_mem hn2)
    have hle : commutator Q ≤ N := Subgroup.commutator_le.2 fun g _ h' _ => hcomm g h'
    rw [hperf.commutator_eq_top] at hle
    exact eq_top_iff.mpr hle

theorem mulAut_eq_one_of_central {Q : Type*} [Group Q] (hq : CFSG.IsQuasisimple Q) (φ : MulAut Q)
    (h : ∀ q, φ q * q⁻¹ ∈ Subgroup.center Q) : φ = 1 := by
  obtain ⟨hperf, -, -⟩ := hq
  have hcomm : ∀ a b : Q, φ ⁅a, b⁆ = ⁅a, b⁆ := by
    intro a b
    calc φ ⁅a, b⁆ = ⁅φ a, φ b⁆ := map_commutatorElement φ a b
      _ = ⁅(φ a * a⁻¹) * a, (φ b * b⁻¹) * b⁆ := by simp
      _ = ⁅a, b⁆ := quot_commutator_central_mul (h a) (h b) a b
  have hle : commutator Q ≤ MonoidHom.eqLocus φ.toMonoidHom (MonoidHom.id Q) :=
    Subgroup.commutator_le.2 fun a _ b _ => hcomm a b
  have htop : MonoidHom.eqLocus φ.toMonoidHom (MonoidHom.id Q) = ⊤ := by
    rw [eq_top_iff]
    intro q _
    exact hle (by rw [hperf.commutator_eq_top]; trivial)
  ext q
  have : q ∈ MonoidHom.eqLocus φ.toMonoidHom (MonoidHom.id Q) := htop ▸ Subgroup.mem_top q
  simpa using this

theorem conj_eq_one_iff {Q : Type*} [Group Q] (q : Q) :
    MulAut.conj q = 1 ↔ q ∈ Subgroup.center Q := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro hq g
    have hg := congrArg (fun φ : MulAut Q => φ g) hq
    simp only [MulAut.conj_apply, MulAut.one_apply] at hg
    exact (mul_inv_eq_iff_eq_mul.mp hg).symm
  · intro hq
    ext g
    rw [MulAut.one_apply, MulAut.conj_apply, ← hq g, mul_inv_cancel_right]

end CFSG.RankThree.PartTwo.Sec15.F153L3C2
