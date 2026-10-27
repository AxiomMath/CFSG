module

public import Mathlib.Algebra.Group.End

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps86

private theorem comm_comm_eq_one {X : Type*} [CommGroup X] (hX : ∀ x : X, x * x = 1)
    (t p : MulAut X) (htt : ∀ x, t (t x) = x) (hpp : ∀ x, p (p x) = x)
    (h5 : ∀ x, p (t (p (t (p x)))) = t (p (t x)))
    (TI1 : ∀ x y : X, x * t x = y * p (t (p y)) → x * t x = 1)
    (TI2 : ∀ x y : X, x * p x = y * t (p (t y)) → x * p x = 1) (z : X) :
    (z * t z) * p (z * t z) = 1 := by
  have hapa : p (z * t z) * t (p (z * t z)) = 1 := by
    refine TI1 _ (p z * t (p z)) ?_
    simp only [map_mul, hpp, h5]
    ac_rfl
  have hfix : t (p (z * t z)) = p (z * t z) := mul_left_cancel (hapa.trans (hX _).symm)
  have hfix' : t (z * t z) = z * t z := by rw [map_mul, htt, mul_comm]
  refine TI2 _ (z * t z) ?_
  rw [hfix', hfix]

theorem d8_trivial {X : Type*} [CommGroup X] (hX : ∀ x : X, x * x = 1) (t p : MulAut X)
    (ht : t * t = 1) (hp : p * p = 1) (h4 : (t * p) ^ 4 = 1)
    (TI1 : ∀ x y : X, x * t x = y * (p * t * p) y → x * t x = 1)
    (TI2 : ∀ x y : X, x * p x = y * (t * p * t) y → x * p x = 1) :
    (t * p) ^ 2 = 1 := by
  have htt : ∀ x, t (t x) = x := fun x => DFunLike.congr_fun ht x
  have hpp : ∀ x, p (p x) = x := fun x => DFunLike.congr_fun hp x
  have h8 : ∀ x, t (p (t (p (t (p (t (p x))))))) = x := fun x => by
    simpa only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply]
      using DFunLike.congr_fun h4 x
  have h4' : ∀ y, t (p (t (p y))) = p (t (p (t y))) := fun y => by
    simpa only [hpp, htt] using h8 (p (t (p (t y))))
  have h5 : ∀ x, p (t (p (t (p x)))) = t (p (t x)) := fun x => by rw [← h4' (p x), hpp]
  have h5' : ∀ x, t (p (t (p (t x)))) = p (t (p x)) := fun x => by rw [h4' (t x), htt]
  have hcomm : ∀ x, t (p x) = p (t x) := fun x => by
    have e1 := comm_comm_eq_one hX t p htt hpp h5 TI1 TI2 x
    have e2 := comm_comm_eq_one hX p t hpp htt h5' TI2 TI1 x
    simp only [map_mul] at e1 e2
    have h : x * t x * p x * p (t x) = x * t x * p x * t (p x) := by
      calc x * t x * p x * p (t x) = x * t x * (p x * p (t x)) := mul_assoc _ _ _
        _ = 1 := e1
        _ = x * p x * (t x * t (p x)) := e2.symm
        _ = x * t x * p x * t (p x) := by ac_rfl
    exact (mul_left_cancel h).symm
  refine MulEquiv.ext fun x => ?_
  rw [pow_two, MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, MulAut.one_apply,
    ← hcomm (p x), htt, hpp]

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps86

end
