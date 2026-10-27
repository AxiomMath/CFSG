module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res8ProofSp4
public import CFSG.RankThree.PartTwo.Sec8.Item812Res8ProofShift
import CFSG.RankThree.PartTwo.KFacts.K71Item89

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint.Chevalley

@[expose] def KF89G2TwoTwoLocal : Prop :=
  ∀ (k : Type) [Field k] [Finite k], Nat.card k = 2 →
    TwoLocalThree (perfectResidual (adjointGroup .G2 k))


open Item812Res8 in
theorem kF89G2TwoLocal_of
    (hG2 : KFG2Ord3Inv)
    (h2 : KF89G2TwoTwoLocal) : KF89G2TwoLocal := by
  intro m hm k _ _ hk
  rcases Nat.lt_or_ge m 2 with hm1 | hm2
  · obtain rfl : m = 1 := by omega
    exact h2 k (by rw [hk, pow_one])
  · set H := adjointGroup .G2 k
    have h3k : 3 ≤ Nat.card k := by
      rw [hk]
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
    have hq := CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card k h3k
    have hZ : Subgroup.center H = ⊥ := CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
    have hS : IsSimpleGroup H := CFSG.LieType.Simplicity.isSimpleGroup_of_mulEquiv hq
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
    have h3 : 3 ∣ Nat.card H := by
      rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hk, CFSG.Open.ordG2]
      refine Dvd.dvd.mul_left ?_ _
      have h4' : (2 ^ m) ^ 2 = 4 ^ m := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [h4']
      exact Item87Proof.three_dvd_four_pow_sub_one m
    have hTL : TwoLocalThree H := by
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := H) 3 h3
      have hy3 : y ^ 3 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
      have hy1 : y ≠ 1 := by
        rintro rfl
        rw [orderOf_one] at hy
        omega
      obtain ⟨s, hs1, hs2, hsy⟩ := hG2 m hm k hk y hy
      refine ⟨noThetaNormal_of_isSimpleGroup h3, y, Subgroup.zpowers s, hy3, ?_, ?_, ?_, ?_⟩
      · rw [hZ, Subgroup.mem_bot]
        exact hy1
      · intro h0
        apply hs1
        have : s ∈ Subgroup.zpowers s := Subgroup.mem_zpowers s
        rw [h0, Subgroup.mem_bot] at this
        exact this
      · refine IsPGroup.of_card (n := 1) ?_
        rw [Nat.card_zpowers, orderOf_eq_prime hs2 hs1, pow_one]
      · refine mem_normalizer_of_forall_conj_mem _ fun t ht => ?_
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
        have hc : y * s ^ j * y⁻¹ = s ^ j := by
          rw [(Commute.zpow_right (show Commute y s from hsy.symm) j).eq, mul_inv_cancel_right]
        rw [hc]
        exact Subgroup.zpow_mem_zpowers s j
    rw [KFacts.perfectResidual_eq_top_of_isPerfect hq.1]
    exact TwoLocalThree.of_mulEquiv Subgroup.topEquiv hTL

end CFSG.RankThree.PartTwo.Sec8
