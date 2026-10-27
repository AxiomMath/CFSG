module

public import CFSG.Permutation.FiveTransitive.Degree24PrimeSupportIncidence

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction Subgroup

private noncomputable def squareOrderSevenSupportEquiv
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (d : ℕ) :
    OrderPrimeSupportElements X P 7 d ≃
      OrderPrimeSupportElements X P 7 d where
  toFun u := by
    have huPermOrder :
        orderOf (u.1.1 : Equiv.Perm X) = 7 := by
      calc
        orderOf (u.1.1 : Equiv.Perm X) =
            orderOf u.1 :=
          Subgroup.orderOf_coe _
        _ = 7 := u.2.1
    refine ⟨u.1 ^ 2, ?_, ?_⟩
    · exact
        ((show (orderOf u.1).Coprime 2 by
            rw [u.2.1]
            norm_num).orderOf_pow).trans u.2.1
    · change
        ((u.1.1 : Equiv.Perm X) ^ 2).support.card = d
      rw [Equiv.Perm.support_pow_coprime (by
        rw [huPermOrder]
        norm_num)]
      exact u.2.2
  invFun u := by
    have huPermOrder :
        orderOf (u.1.1 : Equiv.Perm X) = 7 := by
      calc
        orderOf (u.1.1 : Equiv.Perm X) =
            orderOf u.1 :=
          Subgroup.orderOf_coe _
        _ = 7 := u.2.1
    refine ⟨u.1 ^ 4, ?_, ?_⟩
    · exact
        ((show (orderOf u.1).Coprime 4 by
            rw [u.2.1]
            norm_num).orderOf_pow).trans u.2.1
    · change
        ((u.1.1 : Equiv.Perm X) ^ 4).support.card = d
      rw [Equiv.Perm.support_pow_coprime (by
        rw [huPermOrder]
        norm_num)]
      exact u.2.2
  left_inv u := by
    apply Subtype.ext
    change (u.1 ^ 2) ^ 4 = u.1
    rw [← pow_mul]
    norm_num
    rw [show 8 = 7 + 1 by norm_num, pow_add]
    have huPow : u.1 ^ 7 = 1 := by
      apply orderOf_dvd_iff_pow_eq_one.mp
      rw [u.2.1]
    simp only [huPow, one_mul, pow_one]
  right_inv u := by
    apply Subtype.ext
    change (u.1 ^ 4) ^ 2 = u.1
    rw [← pow_mul]
    norm_num
    rw [show 8 = 7 + 1 by norm_num, pow_add]
    have huPow : u.1 ^ 7 = 1 := by
      apply orderOf_dvd_iff_pow_eq_one.mp
      rw [u.2.1]
    simp only [huPow, one_mul, pow_one]

private theorem squareOrderSevenSupportEquiv_order
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (d : ℕ)
    (hne : Nonempty (OrderPrimeSupportElements X P 7 d)) :
    orderOf (squareOrderSevenSupportEquiv X P d) = 3 := by
  classical
  let e := squareOrderSevenSupportEquiv X P d
  have hePow : e ^ 3 = 1 := by
    apply Equiv.ext
    intro u
    apply Subtype.ext
    change ((u.1 ^ 2) ^ 2) ^ 2 = u.1
    rw [← pow_mul, ← pow_mul]
    norm_num
    rw [show 8 = 7 + 1 by norm_num, pow_add]
    have huPow : u.1 ^ 7 = 1 := by
      apply orderOf_dvd_iff_pow_eq_one.mp
      rw [u.2.1]
    simp only [huPow, one_mul, pow_one]
  have heNe : e ≠ 1 := by
    obtain ⟨u⟩ := hne
    intro he
    have hsq :
        u.1 ^ 2 = u.1 := by
      have happ :=
        congrArg
          (fun q :
              Equiv.Perm
                (OrderPrimeSupportElements X P 7 d) =>
            (q u).1) he
      exact happ
    have huOne : u.1 = 1 := by
      apply mul_left_cancel (a := u.1)
      simpa only [pow_two, mul_one] using hsq
    have huOrder : orderOf u.1 = 7 := u.2.1
    rw [huOne, orderOf_one] at huOrder
    norm_num at huOrder
  exact orderOf_eq_prime hePow heNe

theorem three_dvd_card_orderSevenSupportElements
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (d : ℕ)
    (hne : Nonempty (OrderPrimeSupportElements X P 7 d)) :
    3 ∣ Nat.card (OrderPrimeSupportElements X P 7 d) := by
  classical
  let e := squareOrderSevenSupportEquiv X P d
  let T : Subgroup
      (Equiv.Perm
        (OrderPrimeSupportElements X P 7 d)) :=
    Subgroup.zpowers e
  have heOrder : orderOf e = 3 :=
    squareOrderSevenSupportEquiv_order X P d hne
  have hTcard : Nat.card T = 3 := by
    rw [Nat.card_zpowers, heOrder]
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hTp : IsPGroup 3 T := by
    apply IsPGroup.of_card (n := 1)
    rw [hTcard]
    norm_num
  have hfixedEmpty :
      IsEmpty
        (MulAction.fixedPoints T
          (OrderPrimeSupportElements X P 7 d)) := by
    constructor
    intro z
    have hz :=
      (MulAction.mem_fixedPoints.mp z.2)
        (⟨e, Subgroup.mem_zpowers e⟩ : T)
    have hsq : z.1.1 ^ 2 = z.1.1 := by
      exact congrArg Subtype.val hz
    have huOne : z.1.1 = 1 := by
      apply mul_left_cancel (a := z.1.1)
      simpa only [pow_two, mul_one] using hsq
    have huOrder : orderOf z.1.1 = 7 := z.1.2.1
    rw [huOne, orderOf_one] at huOrder
    norm_num at huOrder
  have hfixedCard :
      Nat.card
          (MulAction.fixedPoints T
            (OrderPrimeSupportElements X P 7 d)) =
        0 := by
    letI := hfixedEmpty
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_eq_zero
  have hmod :=
    hTp.card_modEq_card_fixedPoints
      (OrderPrimeSupportElements X P 7 d)
  rw [hfixedCard, Nat.modEq_zero_iff_dvd] at hmod
  exact hmod

end FiveTransitive.Degree24

end CFSG
