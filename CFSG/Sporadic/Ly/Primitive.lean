
module

public import CFSG.Sporadic.Ly.PrimitiveBase

public import CFSG.Sporadic.Ly.Action

public section

namespace CFSG.Sporadic.Ly

open CFSG.Sporadic.LySchreier CFSG.Sporadic.Ly.Omega MulAction

theorem isPreprimitive :
    IsPreprimitive J (Fin 8835156) := by
  have := ly_certificate.2.2.2.2.2.1
  let f : orbit J opE →[J] Fin 8835156 :=
    { toFun := ptEquiv.symm
      map_smul' := fun g y => by
        change ptEquiv.symm (g • y) = g • ptEquiv.symm y
        rw [smul_def, Equiv.apply_symm_apply] }
  exact IsPreprimitive.of_surjective (f := f) ptEquiv.symm.surjective

theorem a_ne_one : a ≠ 1 := by
  intro h
  have hc := card_closure_le (x := b) (by norm_num) b_pow_five
  rw [← h, closure_ab, Subgroup.card_top, ly_certificate.1] at hc
  omega

theorem b_ne_one : b ≠ 1 := by
  intro h
  have hc := card_closure_le (x := a) (n := 2) (by norm_num) (by rw [pow_two]; exact a_mul_self)
  have e : ({a, b} : Set J) = {1, a} := by rw [h, Set.pair_comm]
  rw [← e, closure_ab, Subgroup.card_top, ly_certificate.1] at hc
  omega

theorem orderOf_a : orderOf a = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact a_mul_self) a_ne_one

theorem orderOf_b : orderOf b = 5 :=
  orderOf_eq_prime b_pow_five b_ne_one

theorem orderOf_conj :
    orderOf (a * (gConj⁻¹ * b * gConj)) = 67 := by
  have : Fact (Nat.Prime 67) := ⟨by norm_num⟩
  refine orderOf_eq_prime ?_ ?_
  · apply mat_injective
    rw [mat_npow, mat_conj, mX_pow, mat_one]
  · intro h
    have e : gConj⁻¹ * b * gConj = a := by
      calc gConj⁻¹ * b * gConj = a⁻¹ * (a * (gConj⁻¹ * b * gConj)) := by group
        _ = a := by rw [h, mul_one, a_inv]
    have hb : b = gConj * a * gConj⁻¹ := by rw [← e]; group
    have h2 : b ^ 2 = 1 := by
      rw [hb, pow_two]
      calc gConj * a * gConj⁻¹ * (gConj * a * gConj⁻¹) = gConj * (a * a) * gConj⁻¹ := by group
        _ = 1 := by rw [a_mul_self, mul_one, mul_inv_cancel]
    apply b_ne_one
    have h5 := b_pow_five
    calc b = b ^ 5 * (b ^ 2)⁻¹ * (b ^ 2)⁻¹ := by group
      _ = 1 := by rw [h5, h2, inv_one, mul_one, mul_one]

theorem isSimpleGroup_J : IsSimpleGroup J := ly_certificate.2.1

theorem card_J : Nat.card J = 51765179004000000 :=
  ly_certificate.1

theorem isSimpleGroup_Ly :
    IsSimpleGroup Blueprint.NativeSporadic.Ly :=
  @MulEquiv.isSimpleGroup _ _ _ _ isSimpleGroup_J lyEquivJ

theorem card_Ly' :
    Nat.card Blueprint.NativeSporadic.Ly = 51765179004000000 := by
  rw [Nat.card_congr lyEquivJ.toEquiv, card_J]

end CFSG.Sporadic.Ly
