module

public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.SpecificGroups.Quaternion

public section

namespace CFSG.RankThree.GroupTheory

theorem zmod_two_eq_zero_or_eq_one (e : ZMod 2) : e = 0 ∨ e = 1 := by
  revert e
  decide

@[expose] def quaternionDihedralNegation :
    Multiplicative (ZMod 2) →* MulAut (Multiplicative (ZMod 4)) where
  toFun e := if Multiplicative.toAdd e = 0 then 1 else MulEquiv.inv (Multiplicative (ZMod 4))
  map_one' := by simp
  map_mul' e f := by
    have hinv : MulEquiv.inv (Multiplicative (ZMod 4)) * MulEquiv.inv (Multiplicative (ZMod 4)) =
        1 := MulEquiv.ext fun x => inv_inv x
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    induction e using Multiplicative.rec with | ofAdd a =>
    induction f using Multiplicative.rec with | ofAdd b =>
    rcases zmod_two_eq_zero_or_eq_one a with rfl | rfl <;>
      rcases zmod_two_eq_zero_or_eq_one b with rfl | rfl <;>
      simp [← ofAdd_add, hinv, h11]

theorem quaternionDihedralNegation_apply (e : ZMod 2) (j : ZMod 4) :
    quaternionDihedralNegation (Multiplicative.ofAdd e) (Multiplicative.ofAdd j) =
      Multiplicative.ofAdd ((-1) ^ e.val * j) := by
  rcases zmod_two_eq_zero_or_eq_one e with rfl | rfl
  · simp [quaternionDihedralNegation]
  · simp [quaternionDihedralNegation, ZMod.val_one]

abbrev QuaternionDihedralD : Type :=
  Multiplicative (ZMod 4) ⋊[quaternionDihedralNegation] Multiplicative (ZMod 2)

theorem quaternionDihedralD_mul (i j : ZMod 4) (e f : ZMod 2) :
    (⟨Multiplicative.ofAdd i, Multiplicative.ofAdd e⟩ : QuaternionDihedralD) *
        ⟨Multiplicative.ofAdd j, Multiplicative.ofAdd f⟩ =
      ⟨Multiplicative.ofAdd (i + (-1) ^ e.val * j), Multiplicative.ofAdd (e + f)⟩ := by
  ext
  · simp only [SemidirectProduct.mul_left, quaternionDihedralNegation_apply]
    rfl
  · rfl

theorem card_quaternionDihedralD : Nat.card QuaternionDihedralD = 8 := by
  rw [Nat.card_congr SemidirectProduct.equivProd]
  simp

@[expose] def quaternionDihedralZQ : QuaternionGroup 2 := QuaternionGroup.a 2

@[expose] def quaternionDihedralZD : QuaternionDihedralD :=
  ⟨Multiplicative.ofAdd 2, Multiplicative.ofAdd 0⟩

theorem quaternionDihedralZQ_mem_center :
    quaternionDihedralZQ ∈ Subgroup.center (QuaternionGroup 2) := by
  rw [Subgroup.mem_center_iff]
  decide

theorem quaternionDihedralZD_mem_center :
    quaternionDihedralZD ∈ Subgroup.center QuaternionDihedralD := by
  rw [Subgroup.mem_center_iff]
  rintro ⟨n, g⟩
  induction n using Multiplicative.rec with | ofAdd j =>
  induction g using Multiplicative.rec with | ofAdd e =>
  rw [quaternionDihedralZD, quaternionDihedralD_mul, quaternionDihedralD_mul, ZMod.val_zero,
    pow_zero, one_mul, add_zero, zero_add]
  have h2 : (-1 : ZMod 4) ^ e.val * 2 = 2 := by
    rcases zmod_two_eq_zero_or_eq_one e with rfl | rfl
    · simp
    · rw [ZMod.val_one]
      decide
  rw [h2, add_comm]

theorem orderOf_quaternionDihedralZ :
    orderOf (quaternionDihedralZQ, quaternionDihedralZD) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime
  · refine Prod.ext ?_ ?_
    · change quaternionDihedralZQ ^ 2 = 1
      decide
    · change quaternionDihedralZD ^ 2 = 1
      have h4 : (2 : ZMod 4) + 2 = 0 := by decide
      rw [pow_two, quaternionDihedralZD, quaternionDihedralD_mul, ZMod.val_zero, pow_zero, one_mul,
        h4, add_zero]
      rfl
  · intro h
    exact absurd (congrArg Prod.fst h) (by decide)

abbrev quaternionDihedralDiagonal : Subgroup (QuaternionGroup 2 × QuaternionDihedralD) :=
  Subgroup.zpowers (quaternionDihedralZQ, quaternionDihedralZD)

instance quaternionDihedralDiagonal_normal : quaternionDihedralDiagonal.Normal :=
  Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr (by
    rw [Subgroup.center_prod]
    exact ⟨quaternionDihedralZQ_mem_center, quaternionDihedralZD_mem_center⟩))

abbrev QD32 : Type := (QuaternionGroup 2 × QuaternionDihedralD) ⧸ quaternionDihedralDiagonal

theorem card_QD32 : Nat.card QD32 = 32 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup quaternionDihedralDiagonal
  rw [Nat.card_zpowers, orderOf_quaternionDihedralZ, Nat.card_prod, card_quaternionDihedralD,
    Nat.card_eq_fintype_card (α := QuaternionGroup 2), QuaternionGroup.card] at h
  change Nat.card ((QuaternionGroup 2 × QuaternionDihedralD) ⧸ quaternionDihedralDiagonal) = 32
  omega

end CFSG.RankThree.GroupTheory
