module

public import CFSG.Timmesfeld.Bridge.Asc72Basic

public section

namespace CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type*} [Group G] {D : Set G}

theorem IsOddTransp.commute_iff_of_mul_mem (hD : IsOddTransp D) {d e : G} (hd : d ∈ D)
    (he : e ∈ D) (hne : d ≠ e) (hc : Commute d e) (hde : d * e ∈ D) :
    ∀ w ∈ D, (Commute w d ↔ Commute w e) := by
  intro w hw
  have hdd : d * d = 1 := hD.mul_self_eq_one hd
  have hee : e * e = 1 := hD.mul_self_eq_one he
  have hd1 : d ≠ d * e := fun h => hD.ne_one he (by
    have : d * e = d * 1 := by rw [mul_one]; exact h.symm
    exact mul_left_cancel this)
  have he1 : e ≠ d * e := fun h => hD.ne_one hd (by
    have : d * e = 1 * e := by rw [one_mul]; exact h.symm
    exact mul_right_cancel this)
  have h2 := hD.commute_mul_iff hd hde hw hd1 ((Commute.refl d).mul_right hc)
  have h3 := hD.commute_mul_iff he hde hw he1 (hc.symm.mul_right (Commute.refl e))
  have e1 : d * (d * e) = e := by rw [← mul_assoc, hdd, one_mul]
  have e2 : e * (d * e) = d := by rw [hc.eq, ← mul_assoc, hee, one_mul]
  rw [e1] at h2
  rw [e2] at h3
  exact ⟨fun h => (h3.mp h).1, fun h => (h2.mp h).1⟩

end CFSG.Timmesfeld.Bridge.Asc72

