module

public import CFSG.Timmesfeld.Bridge.RootStructQMain
public import CFSG.Timmesfeld.Bridge.Asc72Triangle

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72

variable {X : Type} [Group X]

theorem pow_four_eq_one_of_three {x y t : X}
    (hx : x * x = 1) (hy : y * y = 1) (ht : t * t = 1)
    (hxt : Commute x t) (hxy : (x * y) ^ 3 = 1) (hty : (t * y) ^ 3 = 1) :
    (x * t * y) ^ 4 = 1 := by
  have hxx : x * x = 1 := hx
  have hyy : y * y = 1 := hy
  have htt : t * t = 1 := ht
  have htx : t * x = x * t := hxt.eq.symm
  have h5 : y * x * y = x * y * x := RootStructQ.braid_of_pow_three hx hy hxy
  have h6 : t * y * t = y * t * y := (RootStructQ.braid_of_pow_three ht hy hty).symm
  have htxt : t * x * t = x := by
    calc t * x * t = (x * t) * t := by rw [htx]
      _ = x * (t * t) := by rw [mul_assoc]
      _ = x := by rw [htt, mul_one]
  have e1 : (t * y * t) * (t * x * t) = t * y * x * t := by
    calc (t * y * t) * (t * x * t) = t * y * (t * t) * x * t := by group
      _ = t * y * x * t := by simp [htt]
  have h7 : t * y * x * t = y * t * y * x := by
    calc t * y * x * t = (t * y * t) * (t * x * t) := e1.symm
      _ = (y * t * y) * x := by rw [h6, htxt]
      _ = y * t * y * x := rfl
  rw [show (x * t * y) ^ 4 = x * t * y * x * t * y * x * t * y * x * t * y by
    simp only [pow_succ, pow_two]; group]
  calc x * t * y * x * t * y * x * t * y * x * t * y
      = x * (t * y * x * t) * (y * x * t * y * x * t * y) := by group
    _ = x * (y * t * y * x) * (y * x * t * y * x * t * y) := by rw [h7]
    _ = x * y * t * y * x * y * x * t * y * x * t * y := by group
    _ = x * y * t * (y * x * y) * (x * t * y * x * t * y) := by group
    _ = x * y * t * (x * y * x) * (x * t * y * x * t * y) := by rw [h5]
    _ = x * y * t * x * y * x * x * t * y * x * t * y := by group
    _ = x * y * t * x * y * (x * x) * (t * y * x * t * y) := by group
    _ = x * y * t * x * y * ((1 : X)) * (t * y * x * t * y) := by rw [hxx]
    _ = x * y * t * x * y * t * y * x * t * y := by group
    _ = x * y * (t * x) * (y * t * y * x * t * y) := by group
    _ = x * y * (x * t) * (y * t * y * x * t * y) := by rw [htx]
    _ = x * y * x * t * y * t * y * x * t * y := by group
    _ = x * y * x * t * y * (t * y * x * t) * (y) := by group
    _ = x * y * x * t * y * (y * t * y * x) * (y) := by rw [h7]
    _ = x * y * x * t * y * y * t * y * x * y := by group
    _ = x * y * x * t * (y * y) * (t * y * x * y) := by group
    _ = x * y * x * t * ((1 : X)) * (t * y * x * y) := by rw [hyy]
    _ = x * y * x * t * t * y * x * y := by group
    _ = x * y * x * (t * t) * (y * x * y) := by group
    _ = x * y * x * ((1 : X)) * (y * x * y) := by rw [htt]
    _ = x * y * x * y * x * y := by group
    _ = x * (y * x * y) * (x * y) := by group
    _ = x * (x * y * x) * (x * y) := by rw [h5]
    _ = x * x * y * x * x * y := by group
    _ = (1 : X) * (x * x) * (y * x * x * y) := by group
    _ = (1 : X) * ((1 : X)) * (y * x * x * y) := by rw [hxx]
    _ = y * x * x * y := by group
    _ = y * (x * x) * (y) := by group
    _ = y * ((1 : X)) * (y) := by rw [hxx]
    _ = y * y := by group
    _ = (1 : X) * (y * y) * ((1 : X)) := by group
    _ = (1 : X) * ((1 : X)) * ((1 : X)) := by rw [hyy]
    _ = (1 : X) := by group

private theorem commute_of_sq_one {a b : X} (ha : a * a = 1) (hb : b * b = 1)
    (h2 : (a * b) ^ 2 = 1) : Commute a b := by
  have h2' : (a * b) * (a * b) = 1 := by simpa [pow_two] using h2
  show a * b = b * a
  rw [← inv_eq_of_mul_eq_one_right h2', mul_inv_rev,
    inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right hb]

theorem orderOf_mul_dvd_four_of_threeTransposition [Finite X] {Θ : Set X}
    (hodd : IsOddTransp Θ)
    (h3 : ∀ d ∈ Θ, ∀ e ∈ Θ, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    {x y t : X} (htri : IsTriangle Θ x y t) :
    orderOf (x * t * y) ∣ 4 := by
  have hx : x * x = 1 := hodd.mul_self_eq_one htri.1
  have ht : t * t = 1 := hodd.mul_self_eq_one htri.2.1
  have hy : y * y = 1 := hodd.mul_self_eq_one htri.2.2.1
  have hxt : Commute x t := htri.2.2.2.2.1
  have hnc_xy : ¬ Commute x y := htri.2.2.2.2.2.1
  have hnc_ty : ¬ Commute t y := htri.2.2.2.2.2.2
  have hxy3 : (x * y) ^ 3 = 1 := by
    have hmem : orderOf (x * y) = 1 ∨ orderOf (x * y) = 2 ∨ orderOf (x * y) = 3 := by
      simpa using h3 x htri.1 y htri.2.2.1
    rcases hmem with h1 | h2 | h3'
    · have he := orderOf_eq_one_iff.mp h1
      exact absurd (commute_of_sq_one hx hy (by rw [he]; simp)) hnc_xy
    · exact absurd (commute_of_sq_one hx hy
        (orderOf_dvd_iff_pow_eq_one.mp (by rw [h2]))) hnc_xy
    · simpa [h3'] using pow_orderOf_eq_one (x * y)
  have hty3 : (t * y) ^ 3 = 1 := by
    have hmem : orderOf (t * y) = 1 ∨ orderOf (t * y) = 2 ∨ orderOf (t * y) = 3 := by
      simpa using h3 t htri.2.1 y htri.2.2.1
    rcases hmem with h1 | h2 | h3'
    · have he := orderOf_eq_one_iff.mp h1
      exact absurd (commute_of_sq_one ht hy (by rw [he]; simp)) hnc_ty
    · exact absurd (commute_of_sq_one ht hy
        (orderOf_dvd_iff_pow_eq_one.mp (by rw [h2]))) hnc_ty
    · simpa [h3'] using pow_orderOf_eq_one (t * y)
  exact orderOf_dvd_iff_pow_eq_one.mpr
    (pow_four_eq_one_of_three hx hy ht hxt hxy3 hty3)

end CFSG.OddTranspositions
