module

public import CFSG.Timmesfeld.Exceptional.CaseILocal
public import CFSG.Timmesfeld.Moufang.Three

public section

namespace CFSG.Timmesfeld.Moufang

variable {G : Type*} [Group G] {D : Set G}

theorem plane_of_levi (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hD : IsRootInvolutionSet D)
    {x y d z : G} (hx : x ∈ D) (hy : y ∈ D) (hd : d ∈ D) (hz : z ∈ D)
    (h3 : orderOf (x * y) = 3) (hdx : Commute d x) (hdy : Commute d y) (hxz : Commute x z)
    (hxzD : x * z ∈ D) (hdz : Commute d z) (hdzD : d * z ∈ D) :
    y * z * y ∈ D ∧ Commute d (y * z * y) ∧ Commute z (y * z * y) ∧ z * (y * z * y) ∈ D ∧
      d * (y * z * y) ∈ D ∧ d * z * (y * z * y) ∈ D := by
  have hxy : ¬ Commute x y := by
    intro hc
    have h2 := orderOf_dvd_of_pow_eq_one ((commute_iff_mul_sq_eq_one (hD.mul_self_eq_one hx)
      (hD.mul_self_eq_one hy)).1 hc)
    rw [h3] at h2
    exact absurd h2 (by decide)
  have hodd : Odd (orderOf (x * y)) := by rw [h3]; decide
  have h4 : orderOf (z * y) = 4 :=
    orderOf_mul_eq_four_of_collinear_of_commute hD hy hz hd hxy hodd hxz hxzD hdz hdzD hdy
  obtain ⟨hwD, hzw, -, hyzy⟩ := sq_mem_of_orderOf_eq_four hD hz hy h4
  have hyi := hD.inv_eq hy
  have hz2 := hD.mul_self_eq_one hz
  have hz1D : y * z * y ∈ D := by
    have := conj_mem_of_isClass hclass y hz
    rwa [hyi] at this
  have hz1 : y * z * y = z * (z * y) ^ 2 := hyzy
  have hzz1 : z * (y * z * y) = (z * y) ^ 2 := by rw [hz1, ← mul_assoc, hz2, one_mul]
  have hdz1 : Commute d (y * z * y) := (hdy.mul_right hdz).mul_right hdy
  have hzz1c : Commute z (y * z * y) := by rw [hz1]; exact (Commute.refl z).mul_right hzw
  have hdz1D : d * (y * z * y) ∈ D := by
    have := conj_mem_of_isClass hclass y hdzD
    rwa [hyi, show y * (d * z) * y = d * (y * z * y) by
      rw [← mul_assoc, ← hdy.eq]; group] at this
  have hnat := mul_sq_sq_eq_of_orderOf_eq_three hclass hD hx hy hz h3 hxz hxzD h4
  have hxw : x * (y * z * y) * x = z * (y * z * y) := by
    rw [hzz1]
    have hw2 := hD.mul_self_eq_one hwD
    have hx2 := hD.mul_self_eq_one hx
    have h1 : x * ((z * y) ^ 2) * x = (z * y) ^ 2 * z := by
      calc x * ((z * y) ^ 2) * x = (z * y) ^ 2 * ((z * y) ^ 2 * x) ^ 2 := by
            rw [pow_two ((z * y) ^ 2 * x)]
            calc x * (z * y) ^ 2 * x = ((z * y) ^ 2 * (z * y) ^ 2) * x * (z * y) ^ 2 * x := by
                  rw [hw2, one_mul]
              _ = (z * y) ^ 2 * ((z * y) ^ 2 * x * ((z * y) ^ 2 * x)) := by group
        _ = (z * y) ^ 2 * z := by rw [hnat]
    have hxzx : x * z * x = z := by rw [hxz.eq, mul_assoc, hx2, mul_one]
    calc x * (y * z * y) * x = x * z * x * (x * (z * y) ^ 2 * x) := by
          rw [hz1, show x * z * x * (x * (z * y) ^ 2 * x) = x * z * (x * x) * (z * y) ^ 2 * x by
            group, hx2, mul_one]
          group
      _ = z * ((z * y) ^ 2 * z) := by rw [hxzx, h1]
      _ = (z * y) ^ 2 := by rw [← hzw.eq, ← mul_assoc, hz2, one_mul]
  refine ⟨hz1D, hdz1, hzz1c, by rw [hzz1]; exact hwD, hdz1D, ?_⟩
  have := conj_mem_of_isClass hclass x hdz1D
  rwa [hD.inv_eq hx, show x * (d * (y * z * y)) * x = d * (x * (y * z * y) * x) by
    rw [← mul_assoc, ← hdx.eq]; group, hxw, ← mul_assoc] at this

theorem exists_levi_conj (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) {x y b z d : G}
    (hx : x ∈ D) (hy : y ∈ D) (hb : b ∈ D) (hz : z ∈ D) (hd : d ∈ D) (hxy : ¬ Commute x y)
    (hoddxy : Odd (orderOf (x * y))) (hbx : Commute b x) (hby : Commute b y)
    (hxz : Commute x z) (hxzD : x * z ∈ D) (hbz : Commute b z) (hbzD : b * z ∈ D) :
    ∃ x' ∈ D, ∃ y' ∈ D, ∃ z' ∈ D, ¬ Commute x' y' ∧ Odd (orderOf (x' * y')) ∧
      Commute d x' ∧ Commute d y' ∧ Commute x' z' ∧ x' * z' ∈ D ∧ Commute d z' ∧
      d * z' ∈ D := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 (isConj_of_isClass hclass hb hd)
  have hc : ∀ u v : G, Commute u v → Commute (g * u * g⁻¹) (g * v * g⁻¹) :=
    fun u v h => (Commute.conj_iff g).2 h
  have hm : ∀ u v : G, g * u * g⁻¹ * (g * v * g⁻¹) = g * (u * v) * g⁻¹ := fun u v => by group
  refine ⟨_, conj_mem_of_isClass hclass g hx, _, conj_mem_of_isClass hclass g hy, _,
    conj_mem_of_isClass hclass g hz, fun h => hxy ((Commute.conj_iff g).1 h), ?_, hc _ _ hbx,
    hc _ _ hby, hc _ _ hxz, ?_, hc _ _ hbz, ?_⟩
  · rw [hm, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hoddxy
  · rw [hm]; exact conj_mem_of_isClass hclass g hxzD
  · rw [hm]; exact conj_mem_of_isClass hclass g hbzD

end CFSG.Timmesfeld.Moufang
