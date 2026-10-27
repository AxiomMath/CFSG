module

public import CFSG.RankThree.PartTwo.Sec21.Item211Res2ProofLocal
public import CFSG.RankThree.PartTwo.Sec21.Item211Res3ProofON
import CFSG.RankThree.PartTwo.Sec13.Item137Tools

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.RankThree.Native.ONTriple (GM)
open scoped commutatorElement

@[expose] def Item2130LocalONType : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G) (b : G)
    (U₀ Y : Subgroup G),
    Config2130 G A E U c L → Nat.card (A ⊓ L : Subgroup G) = 9 → Choice2130 A E c L b U₀ Y →
      A ≤ Y → Sec4.IsTripleCover (lBar Y) Blueprint.NativeSporadic.ON

open Item211Res3Proof Item211Res2Proof

theorem item2130LocalON_of
    (hT : Item2130LocalONType) : Item2130LocalON := by
  intro G _ _ A E U c L b U₀ Y hcfg h9 hC hAY
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hON := hT G A E U c L b U₀ Y hcfg h9 hC hAY
  have hAe : IsElemAbelian 3 A := hcfg.pair.mem_S.1.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hA27 : Nat.card A = 3 ^ 3 := by rw [hcfg.card_eq, h9]; norm_num
  have hpairs := mem_lThreeStarPairs_iff.mp hcfg.pair.mem_pair
  have hcA : c ∈ A := hcfg.pair.mem_E.2 hpairs.1.1
  have hbA : b ∈ A := hC.b_mem.1
  have hb1 := hC.b_ne_one
  have hb3 : b ^ 3 = 1 := hAe.2 b hbA
  have hYb : Y ∈ thetaComponentsAt 3 b := lZeroStarAt_subset A b hC.y_mem
  have hq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hYb
  have hYC : Y ≤ Subgroup.centralizer ({b} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hYb
  have hbY : b ∈ Y := hAY hbA
  obtain ⟨hZ, -, -⟩ := Sec13.ON134.center_eq_zpowers hbY hb3 hb1 hYC hON
  obtain ⟨ψ⟩ := Sec13.ON134.nonempty_equiv_model hq.1 hON
  have hZ3 : ∀ z ∈ Subgroup.center (lBar Y), z ^ 3 = 1 := by
    intro z hz
    have h := pow_card_eq_one' (G := Subgroup.center (lBar Y)) (x := ⟨z, hz⟩)
    rw [hON.1] at h
    exact congrArg Subtype.val h
  obtain ⟨b', hb'B, hb'b⟩ : ∃ b' ∈ A ⊓ L, b' ∉ Subgroup.zpowers b := by
    by_contra hall
    push Not at hall
    have h := Subgroup.card_le_of_le (show A ⊓ L ≤ Subgroup.zpowers b from hall)
    rw [h9, Sec13.card_zpowers_of_pow_three hb3 hb1] at h
    norm_num at h
  obtain ⟨w₀, hw₀W, hw₀B, hw₀c⟩ := hcfg.full b' hb'B
  have hBe : ∀ x ∈ A ⊓ L, x ^ 3 = 1 := fun x hx => hAe.2 x hx.1
  obtain ⟨k, hk3, hkc⟩ := exists_pow_conj_of_isPGroup hBe hb'B hw₀B hw₀c
  set w := w₀ ^ k with hw
  have hwB := pow_conj_eq_of_conj_eq hw₀B k
  have hwb : w * b = b * w := by
    have h1 := hwB b hC.b_mem
    calc w * b = w * b * w⁻¹ * w := by group
      _ = b * w := by rw [h1]
  have hwC : Subgroup.zpowers w ≤ Subgroup.centralizer ({b} : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    exact hwb
  have hwY : w ∈ Subgroup.normalizer (Y : Set G) := hC.three_norm _ hk3 hwC (Subgroup.mem_zpowers w)
  have hwA : w ∈ Subgroup.normalizer (A : Set G) := Subgroup.pow_mem _ hw₀W k
  obtain ⟨κ, hκ⟩ := exists_inner_of_commute ψ hbY hZ hwY hwb
  obtain ⟨e, he⟩ := hk3 ⟨w, Subgroup.mem_zpowers w⟩
  have hwe : (⟨w, hwY⟩ : Subgroup.normalizer (Y : Set G)) ^ 3 ^ e = 1 :=
    Subtype.ext (by simpa using congrArg Subtype.val he)
  have hκcen : κ ^ 3 ^ e ∈ Subgroup.center (lBar Y) := by
    rw [Subgroup.mem_center_iff]
    intro q
    have h1 := Sec13.ON134.pow_apply_of_conj hκ (3 ^ e) q
    rw [← map_pow, hwe, map_one, MulAut.one_apply] at h1
    calc q * κ ^ 3 ^ e = κ ^ 3 ^ e * q * (κ ^ 3 ^ e)⁻¹ * κ ^ 3 ^ e := by rw [← h1]
      _ = κ ^ 3 ^ e * q := by group
  have hκe : κ ^ 3 ^ (e + 1) = 1 := by
    rw [pow_succ, pow_mul]
    exact hZ3 _ hκcen
  have hκ3 : IsPGroup 3 (Subgroup.zpowers κ) := by
    intro g
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp g.2
    refine ⟨e + 1, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, ← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      hκe, one_zpow, Subgroup.coe_one]
  set Ā := (A.subgroupOf Y).map (QuotientGroup.mk' (aschbacherSolvableCore 3 Y)) with hĀ
  have hĀ27 := isE27_image hAe hA27 hAY
  have hĀ3 : IsPGroup 3 Ā := fun g => ⟨1, Subtype.ext (by simpa using hĀ27.1.2 g g.2)⟩
  have hκN : κ ∈ Subgroup.normalizer (Ā : Set (lBar Y)) := by
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    obtain ⟨⟨a, haY⟩, haA, rfl⟩ := hn
    have hmem : w * a * w⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp hwA a).mp (Subgroup.mem_subgroupOf.mp haA)
    have hmemY : w * a * w⁻¹ ∈ Y := hAY hmem
    rw [SetLike.mem_coe, ← hκ]
    have e : barAct Y ⟨w, hwY⟩ (QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨a, haY⟩) =
        ((⟨w * a * w⁻¹, hmemY⟩ : Y) : lBar Y) := rfl
    rw [e]
    exact ⟨⟨_, hmemY⟩, Subgroup.mem_subgroupOf.mpr hmem, rfl⟩
  have hH : IsPGroup 3 (Subgroup.zpowers κ ⊔ Ā : Subgroup (lBar Y)) :=
    IsPGroup.to_sup_of_normal_right' hκ3 hĀ3 (Subgroup.zpowers_le.mpr hκN)
  have hcY : c ∈ Y := hAY hcA
  have hb'Y : b' ∈ Y := hAY hb'B.1
  have hcĀ : ((⟨c, hcY⟩ : Y) : lBar Y) ∈ Ā :=
    ⟨⟨c, hcY⟩, Subgroup.mem_subgroupOf.mpr hcA, rfl⟩
  have hcen := comm_mem_center_of_isPGroup ψ hH (Subgroup.mem_sup_left (Subgroup.mem_zpowers κ))
    (Subgroup.mem_sup_right hcĀ)
  have hκc : κ * ((⟨c, hcY⟩ : Y) : lBar Y) * κ⁻¹ =
      ((⟨c, hcY⟩ : Y) : lBar Y) * ((⟨b', hb'Y⟩ : Y) : lBar Y) := by
    rw [← hκ]
    have hmem : w * c * w⁻¹ ∈ Y := by rw [hkc]; exact Y.mul_mem hcY hb'Y
    have e : barAct Y ⟨w, hwY⟩ ((⟨c, hcY⟩ : Y) : lBar Y) =
        ((⟨w * c * w⁻¹, hmem⟩ : Y) : lBar Y) := rfl
    rw [e, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext hkc
  have hcb' : ((⟨c, hcY⟩ : Y) : lBar Y) * ((⟨b', hb'Y⟩ : Y) : lBar Y) =
      ((⟨b', hb'Y⟩ : Y) : lBar Y) * ((⟨c, hcY⟩ : Y) : lBar Y) := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (hcomm c hcA b' hb'B.1)
  have hcomm_eq : ⁅κ, ((⟨c, hcY⟩ : Y) : lBar Y)⁆ = ((⟨b', hb'Y⟩ : Y) : lBar Y) := by
    rw [commutatorElement_def, hκc, hcb', mul_inv_cancel_right]
  rw [hcomm_eq, hZ] at hcen
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hcen
  have hA3 : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAe.2 g g.2)⟩
  have hP3 : IsPGroup 3 (A.subgroupOf Y) := hA3.comap_subtype
  have hinj := CFSG.RankThree.injOn_mk_of_isPGroup Nat.prime_three hP3
  have h1 : (⟨b, hbY⟩ : Y) ^ n = ⟨b', hb'Y⟩ :=
    hinj (Subgroup.zpow_mem _ (Subgroup.mem_subgroupOf.mpr hbA) n)
      (Subgroup.mem_subgroupOf.mpr hb'B.1) (by rw [map_zpow]; exact hn)
  apply hb'b
  have h2 : b ^ n = b' := by
    have := congrArg Subtype.val h1
    rwa [Subgroup.coe_zpow] at this
  rw [← h2]
  exact Subgroup.zpow_mem_zpowers b n

end CFSG.RankThree.PartTwo.Sec21
