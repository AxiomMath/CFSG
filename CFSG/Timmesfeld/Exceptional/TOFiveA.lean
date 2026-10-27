module

public import CFSG.Timmesfeld.Exceptional.Distance
public import CFSG.Timmesfeld.Exceptional.Counting
public import CFSG.Timmesfeld.Exceptional.NearPolygon

public section

namespace CFSG.Timmesfeld.Moufang

variable {G : Type*} [Group G] {D : Set G}

theorem exists_reflection (hD : IsRootInvolutionSet D)
    (hconj : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D) {p c : G} (hp : p ∈ D) (hc : c ∈ D)
    (hodd : Odd (orderOf (p * c))) : ∃ e ∈ D, e * p * e = c ∧ e * c * e = p := by
  obtain ⟨k, hk⟩ := hodd
  have hp2 := hD.mul_self_eq_one hp
  have hpp : ∀ a : G, p * (p * a) = a := fun a => by rw [← mul_assoc, hp2, one_mul]
  obtain ⟨r, hr⟩ : ∃ r, p * c = r := ⟨_, rfl⟩
  rw [hr] at hk
  have hrinv : r⁻¹ = c * p := by rw [← hr, mul_inv_rev, hD.inv_eq hp, hD.inv_eq hc]
  have hpr : ∀ m : ℕ, p * r ^ m * p = (r ^ m)⁻¹ := by
    intro m
    have h1 : p * r * p⁻¹ = r⁻¹ := by
      rw [hrinv, hD.inv_eq hp, ← hr, ← mul_assoc, hp2, one_mul]
    rw [← inv_pow, ← h1, conj_pow, hD.inv_eq hp]
  have hconjr : ∀ m : ℕ, r ^ m * p * (r ^ m)⁻¹ = r ^ (m + m) * p := by
    intro m
    rw [← hpr m, pow_add]
    simp only [mul_assoc, hpp]
  have hr1 : r ^ (2 * k + 1) = 1 := hk ▸ pow_orderOf_eq_one r
  have hrk : r ^ (k + k) = r⁻¹ := by
    rw [← two_mul]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hr1)
  have he2 : r ^ k * p * (r ^ k * p) = 1 := by
    rw [show r ^ k * p * (r ^ k * p) = r ^ k * (p * r ^ k * p) by simp only [mul_assoc], hpr,
      mul_inv_cancel]
  have hep : r ^ k * p * p * (r ^ k * p) = c := by
    calc r ^ k * p * p * (r ^ k * p) = r ^ (k + k) * p := by
          rw [pow_add]
          simp only [mul_assoc, hpp]
      _ = c := by rw [hrk, hrinv, mul_assoc, hp2, mul_one]
  refine ⟨r ^ k * p, ?_, hep, ?_⟩
  ·
    have : r ^ k * p = r ^ (k * (k + 1)) * p * (r ^ (k * (k + 1)))⁻¹ := by
      rw [hconjr]
      congr 1
      rw [show k * (k + 1) + k * (k + 1) = (2 * k + 1) * k + k by ring, pow_add, pow_mul, hr1,
        one_pow, one_mul]
    rw [this]
    exact hconj _ p hp
  ·
    rw [← hep]
    calc r ^ k * p * (r ^ k * p * p * (r ^ k * p)) * (r ^ k * p)
        = r ^ k * p * (r ^ k * p) * p * (r ^ k * p * (r ^ k * p)) := by simp only [mul_assoc]
      _ = p := by rw [he2, one_mul, mul_one]

namespace FarLine

theorem conj_mul_conj {e : G} (he : e * e = 1) (a b : G) :
    e * a * e * (e * b * e) = e * (a * b) * e := by
  have hee : ∀ t : G, e * (e * t) = t := fun t => by rw [← mul_assoc, he, one_mul]
  simp only [mul_assoc, hee]

theorem commute_conj {e a b : G} (he : e * e = 1) (h : Commute a b) :
    Commute (e * a * e) (e * b * e) := by
  have := (Commute.conj_iff e).2 h
  rwa [inv_eq_of_mul_eq_one_right he] at this

theorem orderOf_conj_mul {e : G} (he : e * e = 1) (a b : G) :
    orderOf (e * a * e * (e * b * e)) = orderOf (a * b) := by
  rw [conj_mul_conj he]
  have := orderOf_conj_eq e (a * b)
  rwa [inv_eq_of_mul_eq_one_right he] at this

theorem sq_eq (hD : IsRootInvolutionSet D) (hconj : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D)
    (hNL : NoLevi D) (hNP : NoPolar D) (hPl : ExcNoPlane D) {c y x w : G} (hc : c ∈ D)
    (hy : y ∈ D) (hy2 : y ∉ nbhd D c 2) (hx : x ∈ D) (hyx : Commute y x)
    (hxc : orderOf (x * c) = 4) (hw : (x * c) ^ 2 = w) :
    ¬ Commute y w ∧ orderOf (y * w) = 4 ∧ (y * w) ^ 2 = x := by
  have h := sq_mem_of_orderOf_eq_four hD hx hc hxc
  rw [hw] at h
  obtain ⟨hwD, hxw, hcw, -⟩ := h
  have hyw : ¬ Commute y w := fun h =>
    hy2 (mem_nbhd_succ_of_commute hy ((mem_nbhd_one_iff hc).2 ⟨hwD, hcw.symm⟩) h)
  exact ⟨hyw, hNL.orderOf_eq_four hD hx hy hwD hyx.symm hxw hyw,
    hNL.sq_eq_of_commute hD hconj hNP hPl hy hwD hx hyx.symm hxw hyw⟩

theorem reflect (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hD : IsRootInvolutionSet D)
    (hNL : NoLevi D) (hNP : NoPolar D) (hPl : ExcNoPlane D) (hP1 : ExcP1 D) {c p e y x w v : G}
    (hc : c ∈ D) (hp : p ∈ D) (hp3 : p ∉ nbhd D c 3) (he : e ∈ D) (hep : e * p * e = c)
    (hy : y ∈ D) (hpy : Commute p y) (hx : x ∈ D) (hyx : Commute y x)
    (hxc : orderOf (x * c) = 4) (hw : (x * c) ^ 2 = w) (hv : e * w * e = v) :
    v ∈ collinearSet D p ∧ v ∈ nbhd D c 3 ∧ v ∉ nbhd D c 2 ∧ v ≠ y ∧ v ≠ p * y := by
  have hconj : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D := fun g x hx => conj_mem_of_isClass hclass g hx
  have he2 := hD.mul_self_eq_one he
  have hee : ∀ a : G, e * (e * a) = a := fun a => by rw [← mul_assoc, he2, one_mul]
  have heD : ∀ a ∈ D, e * a * e ∈ D := fun a ha => by
    simpa [hD.inv_eq he] using hconj e a ha
  have hback : ∀ a : G, e * (e * a * e) * e = a := fun a => by
    simp only [mul_assoc, hee, he2, mul_one]
  have hec : e * c * e = p := by rw [← hep, hback]
  have hev : e * v * e = w := by rw [← hv, hback]
  have h := sq_mem_of_orderOf_eq_four hD hx hc hxc
  rw [hw] at h
  obtain ⟨hwD, hxw, hcw, -⟩ := h
  have hy2 : y ∉ nbhd D c 2 := fun h => hp3 (mem_nbhd_succ_of_commute hp h hpy)
  obtain ⟨hyc, -⟩ := (not_mem_nbhd_two_iff hD hNL hc hy).1 hy2
  have hp2 : p ∉ nbhd D c 2 := fun h => hp3 (nbhd_mono (by norm_num) h)
  obtain ⟨-, hoddpc⟩ := (not_mem_nbhd_two_iff hD hNL hc hp).1 hp2
  obtain ⟨hyw, -, hsq⟩ := sq_eq hD hconj hNL hNP hPl hc hy hy2 hx hyx hxc hw
  have hx2 : x ∈ nbhd D c 2 := (mem_nbhd_two_iff hD hNL hc).2 ⟨hx, .inr hxc⟩
  have hy3 : y ∈ nbhd D c 3 := mem_nbhd_succ_of_commute hy hx2 hyx
  have hxp : ¬ Commute x p := fun h => hp3 (mem_nbhd_succ_of_commute hp hx2 h.symm)
  have hxp4 : orderOf (x * p) = 4 := hNL.orderOf_eq_four hD hy hx hp hyx hpy.symm hxp
  have hw1 : w ∈ nbhd D c 1 := (mem_nbhd_one_iff hc).2 ⟨hwD, hcw.symm⟩
  have hvD : v ∈ D := hv ▸ heD w hwD
  have hpv : Commute p v := by
    rw [← hec, ← hv]
    exact commute_conj he2 hcw
  have hvp : v ≠ p := by
    intro h
    have hwc : w = c :=
      mul_left_cancel (mul_right_cancel (by rw [hv, h, hec] : e * w * e = e * c * e))
    exact not_commute_of_orderOf_eq_four (hD.mul_self_eq_one hx) (hD.mul_self_eq_one hc) hxc
      (hwc ▸ hxw)
  have hpvD : p * v ∈ D := hNP p hp v hvD hpv (Ne.symm hvp)
  obtain ⟨x', hx'⟩ : ∃ x', e * x * e = x' := ⟨_, rfl⟩
  have hx'D : x' ∈ D := hx' ▸ heD x hx
  have hvx' : Commute v x' := by
    rw [← hv, ← hx']
    exact commute_conj he2 hxw.symm
  have hx'c : orderOf (x' * c) = 4 := by
    rw [← hx', ← hep, orderOf_conj_mul he2]
    exact hxp4
  have hv3 : v ∈ nbhd D c 3 :=
    mem_nbhd_succ_of_commute hvD ((mem_nbhd_two_iff hD hNL hc).2 ⟨hx'D, .inr hx'c⟩) hvx'
  have hv2 : v ∉ nbhd D c 2 := by
    intro h
    obtain ⟨-, h1 | h1⟩ := (mem_nbhd_two_iff hD hNL hc).1 h
    · have hwp : Commute w p := by
        rw [← hev, ← hec]
        exact commute_conj he2 h1
      exact hp3 (nbhd_mono (by norm_num) (mem_nbhd_succ_of_commute hp hw1 hwp.symm))
    · have hwp : orderOf (p * w) = 4 := by
        rw [orderOf_mul_comm_eq, ← hev, ← hec, orderOf_conj_mul he2]
        exact h1
      exact hp3 (mem_nbhd_add_two_of_orderOf_eq_four hD hp hw1 hwD hwp)
  have hye : ¬ Commute y e := fun h => hyc (by
    rw [← hep]
    exact (h.mul_right hpy.symm).mul_right h)
  have hvy : v ≠ y := by
    intro hvy
    have hwy : w = e * y * e := by rw [← hev, hvy]
    have hx'y : Commute x' y := by
      rw [← hvy]
      exact hvx'.symm
    have hx'w : Commute x' w := by
      rw [hwy, ← hx']
      exact commute_conj he2 hyx.symm
    have hxx' : x' = x :=
      (NoLevi.sq_eq_of_commute hD hconj hNL hNP hPl hy hwD hx'D hx'y hx'w hyw).symm.trans hsq
    have hex : Commute e x := by
      have h1 : e * x * e = x := hx'.trans hxx'
      show e * x = x * e
      calc e * x = e * x * e * e := by rw [mul_assoc (e * x), he2, mul_one]
        _ = x * e := by rw [h1]
    have hyx' : y ≠ x := fun h => hy2 (h ▸ hx2)
    have hex' : e ≠ x := fun h => hye (h ▸ hyx)
    rcases NoLevi.centralizer_cases hD hconj hNL hNP hPl hx he hy hex.symm hyx.symm hex' hyx'
      with h | h | ⟨h4, h⟩
    · exact hye (by rw [h])
    · exact hye (by rw [h]; exact hex.symm.mul_left (Commute.refl e))
    ·
      have hye4 : orderOf (y * e) = 4 := by
        rw [orderOf_mul_comm_eq]
        exact h4
      have h' := (sq_mem_of_orderOf_eq_four hD hy he hye4).2.2.2
      rw [← mul_sq_comm_of_orderOf_eq_four he2 (hD.mul_self_eq_one hy) h4, h] at h'
      exact hyw (by rw [hwy, h']; exact (Commute.refl y).mul_right hyx)
  have hvpy : v ≠ p * y := by
    intro h
    have h3y := orderOf_eq_three_of_mem_nbhd_three hD hNL hNP hP1 hc hy3 hy2
    have h3v := orderOf_eq_three_of_mem_nbhd_three hD hNL hNP hP1 hc hv3 hv2
    rw [h] at h3v hvD
    have hypy : y * (p * y) = p := by
      rw [hpy.eq, ← mul_assoc, hD.mul_self_eq_one hy, one_mul]
    refine false_of_orderOf_three_three_of_line (hD.mul_self_eq_one hy) (hD.mul_self_eq_one hvD)
      (hD.mul_self_eq_one hc) (hpy.symm.mul_right (Commute.refl y)) h3y h3v ?_
    rwa [hypy]
  exact ⟨⟨hvD, hpv, hpvD⟩, hv3, hv2, hvy, hvpy⟩

theorem eq_of_reflect_eq (hD : IsRootInvolutionSet D) (hconj : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D)
    (hNL : NoLevi D) (hNP : NoPolar D) (hPl : ExcNoPlane D) {c e y x x' : G} (hc : c ∈ D)
    (hy : y ∈ D) (hy2 : y ∉ nbhd D c 2) (hx : x ∈ D) (hyx : Commute y x)
    (hxc : orderOf (x * c) = 4) (hx' : x' ∈ D) (hyx' : Commute y x')
    (hx'c : orderOf (x' * c) = 4) (h : e * (x * c) ^ 2 * e = e * (x' * c) ^ 2 * e) : x = x' := by
  have hw : (x * c) ^ 2 = (x' * c) ^ 2 := mul_left_cancel (mul_right_cancel h)
  calc x = (y * (x * c) ^ 2) ^ 2 := (sq_eq hD hconj hNL hNP hPl hc hy hy2 hx hyx hxc rfl).2.2.symm
    _ = (y * (x' * c) ^ 2) ^ 2 := by rw [hw]
    _ = x' := (sq_eq hD hconj hNL hNP hPl hc hy hy2 hx' hyx' hx'c rfl).2.2

theorem ne_mul_reflect (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hD : IsRootInvolutionSet D)
    (hNL : NoLevi D) (hNP : NoPolar D) (hPl : ExcNoPlane D) {c p e y x x' : G} (hc : c ∈ D)
    (he : e ∈ D) (hep : e * p * e = c) (hy : y ∈ D) (hy2 : y ∉ nbhd D c 2) (hx : x ∈ D)
    (hyx : Commute y x) (hxc : orderOf (x * c) = 4) (hx' : x' ∈ D) (hyx' : Commute y x')
    (hx'c : orderOf (x' * c) = 4) : e * (x * c) ^ 2 * e ≠ p * (e * (x' * c) ^ 2 * e) := by
  intro h
  have hconj : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D := fun g x hx => conj_mem_of_isClass hclass g hx
  have he2 := hD.mul_self_eq_one he
  have hee : ∀ a : G, e * (e * a) = a := fun a => by rw [← mul_assoc, he2, one_mul]
  have hw : (x * c) ^ 2 = c * (x' * c) ^ 2 := by
    calc (x * c) ^ 2 = e * (e * (x * c) ^ 2 * e) * e := by simp only [mul_assoc, hee, he2, mul_one]
      _ = e * (p * (e * (x' * c) ^ 2 * e)) * e := by rw [h]
      _ = e * p * e * (x' * c) ^ 2 := by simp only [mul_assoc, he2, mul_one]
      _ = c * (x' * c) ^ 2 := by rw [hep]
  obtain ⟨hyc, hodd⟩ := (not_mem_nbhd_two_iff hD hNL hc hy).1 hy2
  obtain ⟨hw'D, -, hcw', -⟩ := sq_mem_of_orderOf_eq_four hD hx' hc hx'c
  have h1 := (sq_eq hD hconj hNL hNP hPl hc hy hy2 hx' hyx' hx'c rfl).2.1
  have h2 := (sq_eq hD hconj hNL hNP hPl hc hy hy2 hx hyx hxc rfl).2.1
  rw [hw] at h2
  exact Closure.not_special_special_of_opposite hclass hD hc hw'D hcw' hy (fun h => hyc h.symm)
    (by rwa [orderOf_mul_comm_eq]) h1 h2

end FarLine

end CFSG.Timmesfeld.Moufang
