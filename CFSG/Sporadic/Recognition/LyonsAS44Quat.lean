module

public import CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices

private theorem eq_zero_of_pow_val_eq_one {H : Type*} [Group H] {x : H} (hx4 : x ^ 4 = 1)
    (hx2 : x ^ 2 ≠ 1) {k : ZMod 4} (hk : x ^ k.val = 1) : k = 0 := by
  have hord : orderOf x = 4 := by
    have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := x) (by simpa using hx2)
      (by simpa using hx4)
    simpa using h
  have hdvd : orderOf x ∣ k.val := orderOf_dvd_of_pow_eq_one hk
  rw [hord] at hdvd
  exact (ZMod.val_eq_zero k).1 (Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt k))

private theorem sq_eq_one_of_conj_eq_inv_of_commute {H : Type*} [Group H] {x y : H}
    (hyx : y * x * y⁻¹ = x⁻¹) (hc : y * x = x * y) : x ^ 2 = 1 := by
  have h1 : x⁻¹ = x :=
    calc x⁻¹ = y * x * y⁻¹ := hyx.symm
      _ = x * y * y⁻¹ := by rw [hc]
      _ = x := mul_inv_cancel_right x y
  calc x ^ 2 = x * x⁻¹ := by rw [sq, h1]
    _ = 1 := mul_inv_cancel x

theorem nonempty_mulEquiv_quaternionGroup_two {H : Type*} [Group H] [Finite H]
    (hH : Nat.card H = 8) (x y : H) (hx4 : x ^ 4 = 1) (hx2 : x ^ 2 ≠ 1)
    (hyx : y * x * y⁻¹ = x⁻¹) (hy2 : y ^ 2 = x ^ 2) : Nonempty (H ≃* QuaternionGroup 2) := by
  have hinj : Function.Injective (quaternionLift hx4 hyx hy2) := by
    rw [injective_iff_map_eq_one]
    rintro (k | k) hk
    · have hk' : x ^ k.val = 1 := (quaternionLift_a hx4 hyx hy2 k).symm.trans hk
      rw [eq_zero_of_pow_val_eq_one hx4 hx2 hk']
      exact QuaternionGroup.one_def.symm
    · exfalso
      have hk' : y * x ^ k.val = 1 := (quaternionLift_xa hx4 hyx hy2 k).symm.trans hk
      have hy : y = (x ^ k.val)⁻¹ := eq_inv_of_mul_eq_one_left hk'
      have hc : y * x = x * y := by
        rw [hy]
        exact ((Commute.pow_self x k.val).inv_left).eq
      exact hx2 (sq_eq_one_of_conj_eq_inv_of_commute hyx hc)
  have hQ : Nat.card (QuaternionGroup 2) = 8 := by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hbij : Function.Bijective (quaternionLift hx4 hyx hy2) :=
    hinj.bijective_of_nat_card_le (hH.trans hQ.symm).le
  exact ⟨(MulEquiv.ofBijective (quaternionLift hx4 hyx hy2) hbij).symm⟩

end CFSG.Sporadic.Recognition.LyonsSims
