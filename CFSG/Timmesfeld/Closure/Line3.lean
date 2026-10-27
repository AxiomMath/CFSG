module

public import CFSG.Timmesfeld.Closure.Reduction

public section

namespace CFSG.Timmesfeld.Closure

variable {G : Type*} [Group G] {D : Set G}

theorem braid_of_orderOf_eq_three {a y : G} (ha : a * a = 1) (hy : y * y = 1)
    (h3 : orderOf (a * y) = 3) : a * y * a = y * a * y := by
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have h : a * y * a * (y * a * y) = 1 := by
    rw [← pow_orderOf_eq_one (a * y), h3]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [eq_inv_of_mul_eq_one_left h, mul_inv_rev, mul_inv_rev, hainv, hyinv, mul_assoc]

theorem not_orderOf_three_line {d z y : G} (hd : d * d = 1) (hz : z * z = 1) (hy : y * y = 1)
    (hdz : Commute d z) (h1 : orderOf (d * y) = 3) (h2 : orderOf (z * y) = 3)
    (h3 : orderOf (d * z * y) = 3) : False := by
  have hdz2 : (d * z) * (d * z) = 1 := by
    rw [show (d * z) * (d * z) = d * (z * d) * z by group, ← hdz.eq,
      show d * (d * z) * z = (d * d) * (z * z) by group, hd, hz, one_mul]
  have b1 := braid_of_orderOf_eq_three hd hy h1
  have b2 := braid_of_orderOf_eq_three hz hy h2
  have b3 := braid_of_orderOf_eq_three hdz2 hy h3
  have e1 : y * (d * z) * y = (d * y * d) * (z * y * z) := by
    rw [b1, b2]
    calc y * (d * z) * y = y * d * (y * y) * z * y := by rw [hy]; group
      _ = y * d * y * (y * z * y) := by group
  have e2 : y = (z * y * z * d) ^ 2 := by
    have key : (d * y * d) * (z * y * z) = d * z * y * (d * z) := by rw [← e1, b3]
    have k2 : y * d * (z * y * z) = z * y * z * d := by
      calc y * d * (z * y * z) = d * (d * y * d * (z * y * z)) := by
            rw [show d * (d * y * d * (z * y * z)) = (d * d) * y * d * (z * y * z) by group, hd,
              one_mul]
        _ = d * (d * z * y * (d * z)) := by rw [key]
        _ = z * y * z * d := by
            rw [show d * (d * z * y * (d * z)) = (d * d) * z * y * (d * z) by group, hd, one_mul,
              ← mul_assoc]
            calc z * y * d * z = z * y * (d * z) := by group
              _ = z * y * (z * d) := by rw [hdz.eq]
              _ = z * y * z * d := by group
    have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
    have hdinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd
    calc y = (y * d * (z * y * z)) * (d * (z * y * z))⁻¹ := by group
      _ = (z * y * z * d) * (d * (z * y * z))⁻¹ := by rw [k2]
      _ = (z * y * z * d) ^ 2 := by
          rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, hzinv, hdinv, show y⁻¹ = y from
            inv_eq_of_mul_eq_one_right hy, pow_two]
          group
  have ho : orderOf (z * y * z * d) = 3 := by
    have : z * y * z * d = z * (y * d) * z⁻¹ := by
      rw [inv_eq_of_mul_eq_one_right hz, show z * (y * d) * z = z * y * (d * z) by group, hdz.eq]
      group
    rw [this, orderOf_conj_eq, orderOf_mul_comm_eq, h1]
  have hoy : orderOf y = 3 := by
    rw [e2, orderOf_pow' _ two_ne_zero, ho]
    norm_num
  have : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hy)
  rw [hoy] at this
  norm_num at this

theorem commConnected_of_three (h : Hyp G D)
    (h3 : ∀ x ∈ D, ∀ y ∈ D, ¬ Commute x y → Odd (orderOf (x * y)) → orderOf (x * y) = 3) :
    CommConnected D := by
  intro S hSD ⟨x, hx⟩ hclosed y hy
  by_contra hyS
  have hD := h.root
  have hxD := hSD hx
  obtain ⟨d₀, hd₀, e₀, he₀, h4₀⟩ := h.nondeg
  obtain ⟨g, rfl⟩ := isConj_iff.mp (h.isConj hd₀ hxD)
  set e := g * e₀ * g⁻¹ with he
  have heD : e ∈ D := h.conj_mem g he₀
  have h4 : orderOf (g * d₀ * g⁻¹ * e) = 4 := by
    rw [he, show g * d₀ * g⁻¹ * (g * e₀ * g⁻¹) = g * (d₀ * e₀) * g⁻¹ by group, orderOf_conj_eq,
      h4₀]
  obtain ⟨hzD, hxz, hez, -⟩ := sq_mem_of_orderOf_eq_four hD hxD heD h4
  set x' := g * d₀ * g⁻¹
  set z := (x' * e) ^ 2
  have hzS : z ∈ S := hclosed x' hx z hzD hxz
  have hxzD : x' * z ∈ D := mul_sq_mem_of_orderOf_eq_four h.isClass hD hxD heD h4
  have hxzS : x' * z ∈ S := hclosed x' hx _ hxzD (Commute.mul_right (Commute.refl x') hxz)
  have hopp : ∀ w ∈ S, ¬ Commute w y ∧ Odd (orderOf (w * y)) := by
    intro w hw
    have hwD := hSD hw
    rcases commute_or_orderOf_mul_eq_four_or_odd hD hwD hy with hc | h4' | hodd
    · exact absurd (hclosed w hw y hy hc) hyS
    · exfalso
      obtain ⟨hfD, hwf, hyf, -⟩ := sq_mem_of_orderOf_eq_four hD hwD hy h4'
      exact hyS (hclosed _ (hclosed w hw _ hfD hwf) y hy hyf.symm)
    · exact ⟨hodd.2, hodd.1⟩
  obtain ⟨n1, o1⟩ := hopp x' hx
  obtain ⟨n2, o2⟩ := hopp z hzS
  obtain ⟨n3, o3⟩ := hopp _ hxzS
  exact not_orderOf_three_line (hD.mul_self_eq_one hxD) (hD.mul_self_eq_one hzD)
    (hD.mul_self_eq_one hy) hxz (h3 _ hxD y hy n1 o1) (h3 _ hzD y hy n2 o2)
    (h3 _ hxzD y hy n3 o3)

end CFSG.Timmesfeld.Closure
