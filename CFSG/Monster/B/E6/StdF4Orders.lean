module

public import CFSG.Monster.B.E6.StdF4Root
public import CFSG.LieType.Chevalley.RootCommutator

public noncomputable section

namespace CFSG.Monster.B.E6.StdF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Overlap CFSG.Monster.B.Classical

@[expose] def repWord : Fin 5 → List (Fin 4) :=
  ![[], [0], [2, 3, 0, 1, 2, 1, 0], [1, 2, 3, 1, 2, 0, 1, 2, 3, 0, 1, 2, 1, 0],
    [0, 1, 2, 3, 1, 2, 0, 1, 2, 3, 0, 1, 2, 1, 0]]

@[expose] def repRoot : Fin 5 → Fin 6 → ℤ :=
  ![![1, 2, 2, 3, 2, 1], ![1, 1, 2, 3, 2, 1], ![0, 0, 0, 1, 0, 0],
    ![-1, -1, -2, -3, -2, -1], ![-1, -2, -2, -3, -2, -1]]

@[expose] def repLevel : Fin 5 → ℤ := ![2, 1, 0, -1, -2]

theorem foldr_repWord : ∀ i : Fin 5, (repWord i).foldr E6Folded.r E6Folded.θ = repRoot i := by
  decide +kernel

theorem wsmul_repWord
    (i : Fin 5) : wsmul (ncs.wordProd (repWord i)) E6Folded.θ = repRoot i := by
  rw [wsmul_wordProd, foldr_repWord]

theorem form_repRoot : ∀ i : Fin 5, E6Folded.form E6Folded.θ (repRoot i) = repLevel i := by
  decide +kernel

theorem level_repWord
    (i : Fin 5) : level (ncs.wordProd (repWord i)) = repLevel i := by
  rw [level, wsmul_repWord, form_repRoot]

@[expose] def repRootL (i : Fin 5) : Fin Tag.E6.rank → ℤ := toLat (repRoot i)

theorem isRoot_repRootL
    (i : Fin 5) : IsRoot Tag.E6 (repRootL i) := by
  have h := IsRoot.smul isRoot_e6HighestRoot
    ((ncs.wordProd (repWord i) : NW) : WeylGroup TwistTag.E6.tag)
  have e : ((ncs.wordProd (repWord i) : NW) : WeylGroup TwistTag.E6.tag) • e6HighestRoot =
      toLat (repRoot i) := by
    rw [← wsmul_repWord]
    rfl
  rw [e] at h
  exact h

theorem repRootL_zero : repRootL 0 = theta := rfl

theorem height_repRootL_one : 0 < height (repRootL 1) := by decide

theorem height_repRootL_two : 0 < height (repRootL 2) := by decide

theorem commute_rootInvM_of_pos
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ)
    (hpos : 0 < height γ) : Commute rootInvM (pinnedX Tag.E6 K γ 1) :=
  (commute_pinnedX_e6HighestRoot K hγ hpos 1 1).symm

theorem orderOf_mul_of_commute {M : Type*} [Group M] {a b : M} (ha : a * a = 1) (hb : b * b = 1)
    (hab : Commute a b) (hne : a ≠ b) : orderOf (a * b) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [pow_two, mul_assoc, ← mul_assoc b, ← hab.eq, mul_assoc, hb, mul_one, ha]
  · intro h
    apply hne
    rw [mul_eq_one_iff_eq_inv] at h
    rw [h, inv_eq_of_mul_eq_one_right hb]

@[expose] def e2 : Fin Tag.E6.rank → ℤ := Pi.single (⟨1, by decide⟩ : Fin Tag.E6.rank) 1

theorem theta_add_repRootL_three : theta + repRootL 3 = e2 := by decide

theorem theta_ne_repRootL_three : theta ≠ repRootL 3 := by decide

theorem theta_ne_neg_repRootL_three : theta ≠ -repRootL 3 := by decide

theorem isRoot_e2 : IsRoot Tag.E6 e2 := isRoot_single _ _

theorem pinnedX_mul_self
    (α : Fin Tag.E6.rank → ℤ) :
    pinnedX Tag.E6 K α 1 * pinnedX Tag.E6 K α 1 = 1 := by
  rw [← pinnedX_add, one_add_one_eq_two, two_eq_zero_K, pinnedX_zero]

theorem pinnedX_ne_one
    (α : Fin Tag.E6.rank → ℤ) : pinnedX Tag.E6 K α 1 ≠ 1 := by
  intro h
  rw [← pinnedX_zero Tag.E6 K α] at h
  exact one_ne_zero ((pinnedX_injective (τ := Tag.E6) (R := K) α) h)

theorem sq_rootInvM_mul_repRoot_three :
    (rootInvM * pinnedX Tag.E6 K (repRootL 3) 1) ^ 2 = pinnedX Tag.E6 K e2 1 := by
  obtain ⟨hε, hcomm⟩ := (simply_laced_root_commutator_unit Tag.E6 (by decide) isRoot_theta
    (isRoot_repRootL 3) theta_ne_repRootL_three theta_ne_neg_repRootL_three).1
    (theta_add_repRootL_three ▸ isRoot_e2)
  have hc := hcomm K 1 1
  rw [theta_add_repRootL_three, mul_one, mul_one] at hc
  have hε' : ((commConst Tag.E6 theta (repRootL 3) (1, 1) : ℤ) : K) = 1 := by
    rcases hε with h | h <;> rw [h]
    · exact Int.cast_one
    · rw [Int.cast_neg, Int.cast_one, CharTwo.neg_eq]
  rw [hε'] at hc
  rw [← hc, commutatorElement_def, pow_two, rootInvM]
  have h1 : (pinnedX Tag.E6 K theta 1)⁻¹ = pinnedX Tag.E6 K theta 1 :=
    inv_eq_of_mul_eq_one_right (pinnedX_mul_self theta)
  have h2 : (pinnedX Tag.E6 K (repRootL 3) 1)⁻¹ = pinnedX Tag.E6 K (repRootL 3) 1 :=
    inv_eq_of_mul_eq_one_right (pinnedX_mul_self _)
  rw [h1, h2]
  group

theorem orderOf_rootInvM_mul_repRoot_three :
    orderOf (rootInvM * pinnedX Tag.E6 K (repRootL 3) 1) = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := orderOf_eq_prime_pow (p := 2) (n := 1)
    (x := rootInvM * pinnedX Tag.E6 K (repRootL 3) 1) ?_ ?_
  · rw [h]
    norm_num
  · rw [pow_one, sq_rootInvM_mul_repRoot_three]
    exact pinnedX_ne_one _
  · rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, sq_rootInvM_mul_repRoot_three, pow_two,
      pinnedX_mul_self]

theorem repRootL_four : repRootL 4 = -theta := by decide

theorem neg_one_units_K : (-1 : Kˣ) = 1 := Units.ext (by rw [Units.val_neg, Units.val_one,
  CharTwo.neg_eq])

theorem orderOf_xUnit_mul_yUnit
    (i : Fin Tag.E6.rank) :
    orderOf (xUnit Tag.E6 K i 1 * yUnit Tag.E6 K i 1) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set x := xUnit Tag.E6 K i 1
  set y := yUnit Tag.E6 K i 1
  set n := weylElt Tag.E6 K i 1
  have hneg : -(((1 : Kˣ)⁻¹ : Kˣ) : K) = 1 := by
    rw [inv_one, Units.val_one, CharTwo.neg_eq]
  have h1 : x * y * x = n := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, coe_xUnit, coe_yUnit, coe_weylElt, hneg, Units.val_one]
  have h2 : y * x * y = n := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, coe_xUnit, coe_yUnit, coe_weylElt_eq_yOp_mul, hneg,
      Units.val_one]
  have h3 : n * n = 1 := by
    rw [mul_eq_one_iff_eq_inv, weylElt_inv, neg_one_units_K]
  refine orderOf_eq_prime ?_ ?_
  · calc (x * y) ^ 3 = (x * y * x) * (y * x * y) := by
          simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := by rw [h1, h2, h3]
  · intro h
    obtain ⟨-, h2', -⟩ := opposite_simple_root_noncommutativity Tag.E6 K
    apply h2' i 1 1 one_ne_zero one_ne_zero
    rw [← (opposite_simple_root_noncommutativity Tag.E6 K).1]
    have hc : Commute x y := by
      rw [mul_eq_one_iff_eq_inv] at h
      rw [h]
      exact (Commute.refl y).inv_left
    have h' := congrArg Units.val hc.eq
    rw [Units.val_mul, Units.val_mul, coe_xUnit, coe_yUnit] at h'
    rw [h', sub_self, LinearMap.zero_apply]

theorem orderOf_rootInvM_mul_repRoot_four :
    orderOf (rootInvM * pinnedX Tag.E6 K (repRootL 4) 1) = 3 := by
  obtain ⟨v, i, hv⟩ := isRoot_iff_exists_smul_single.1 isRoot_theta
  set N := canonicalRep (coxeterSystem Tag.E6) K v
  have hx : N * xUnit Tag.E6 K i 1 * N⁻¹ = rootInvM := by
    rw [← pinnedX_single, canonicalRep_mul_pinnedX_mul_inv_of_two two_eq_zero_K v
      (isRoot_single _ _), hv]
    rfl
  have hy : N * yUnit Tag.E6 K i 1 * N⁻¹ = pinnedX Tag.E6 K (repRootL 4) 1 := by
    rw [← pinnedX_neg_single, canonicalRep_mul_pinnedX_mul_inv_of_two two_eq_zero_K v
      (isRoot_neg_single _ _), smul_neg, hv, repRootL_four]
  have e : rootInvM * pinnedX Tag.E6 K (repRootL 4) 1 =
      MulAut.conj N (xUnit Tag.E6 K i 1 * yUnit Tag.E6 K i 1) := by
    rw [MulAut.conj_apply, ← hx, ← hy]
    group
  rw [e, MulEquiv.orderOf_eq, orderOf_xUnit_mul_yUnit]

end CFSG.Monster.B.E6.StdF4
