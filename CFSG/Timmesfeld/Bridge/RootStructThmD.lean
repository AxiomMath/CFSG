module

public import CFSG.Timmesfeld.Bridge.RootStructThmA

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

variable {G : Type*} [Group G] {D : Set G}

theorem orderOf_mul_mul_eq_four_of_pow_three {u v c : G} (hu : u * u = 1) (hv : v * v = 1)
    (hc : c * c = 1) (huv : Commute u v) (hne : u ≠ v) (h1 : (u * c) ^ 3 = 1)
    (h2 : (v * c) ^ 3 = 1) : orderOf (c * (u * v)) = 4 := by
  have h4 := Moufang.mul_mul_pow_four_eq_one_of_pow_three hu hv hc huv h1 h2
  have h2' : (u * v * c) ^ 2 ≠ 1 := by
    intro hsq
    have hw2 : u * v * (u * v) = 1 := by
      rw [show u * v * (u * v) = u * (v * u) * v by group, ← huv.eq,
        show u * (u * v) * v = u * u * (v * v) by group, hu, hv, mul_one]
    have hwinv : (u * v)⁻¹ = u * v := inv_eq_of_mul_eq_one_right hw2
    have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc
    have hwc : Commute (u * v) c := by
      have e : u * v * c * (u * v * c) = 1 := by rw [← pow_two]; exact hsq
      have e2 : u * v * c = (u * v * c)⁻¹ := eq_inv_of_mul_eq_one_left e
      rw [mul_inv_rev, hcinv, hwinv] at e2
      exact e2
    have hwu : Commute (u * v) u := (Commute.refl u).mul_left huv.symm
    have hwuc : Commute (u * v) (u * c) := hwu.mul_right hwc
    have hvc : v * c = (u * v) * (u * c) := by
      rw [show u * v * (u * c) = u * (v * u) * c by group, ← huv.eq,
        show u * (u * v) * c = u * u * v * c by group, hu, one_mul]
    have h3 : (v * c) ^ 3 = (u * v) ^ 3 * (u * c) ^ 3 := by rw [hvc, hwuc.mul_pow]
    rw [h2, h1, mul_one, pow_succ, pow_two, hw2, one_mul] at h3
    apply hne
    calc u = u * (u * v) := by rw [← h3, mul_one]
      _ = v := by rw [← mul_assoc, hu, one_mul]
  have hdvd : orderOf (u * v * c) ∣ 4 := orderOf_dvd_of_pow_eq_one h4
  have hnd : ¬ orderOf (u * v * c) ∣ 2 := fun h => h2' (orderOf_dvd_iff_pow_eq_one.1 h)
  have hord : orderOf (u * v * c) = 4 := by
    have hpos : 0 < orderOf (u * v * c) := Nat.pos_of_dvd_of_pos hdvd (by norm_num)
    have hle : orderOf (u * v * c) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : orderOf (u * v * c) <;> simp_all
  rw [orderOf_mul_comm_eq, hord]

theorem exists_orderOf_mul_eq_three_of_oneOpposite (h : Hyp G D) (hc : RootClosure D)
    (hs : SpecialClosure D) (hQ : Moufang.CommLambda D) {b x : G} (hb : b ∈ D) (hx : x ∈ D)
    (hxb : ¬ Commute x b) (hodd : Odd (orderOf (x * b))) (hbx : OneOpposite D b x) :
    ∃ b' ∈ rootSet D b, orderOf (x * b') = 3 := by
  obtain ⟨e, he, hbe, hbeD, h4⟩ := hbx
  have hebD : e * b ∈ D := by rw [← hbe.eq]; exact hbeD
  exact exists_orderOf_mul_eq_three_of_frame h hc hs hx hb he hxb hodd hbe.symm h4
    (frameCondition_of_collinear h.isClass h.root hQ hx hb he hxb hodd hbe.symm hebD h4)
    (mem_rootSet_self hx)

end CFSG.Timmesfeld.Bridge
