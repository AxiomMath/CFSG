module

public import CFSG.Timmesfeld.Exceptional.Residual
public import CFSG.Timmesfeld.Closure.LS

public section

namespace CFSG.Timmesfeld.Moufang

variable {G : Type*} [Group G] {D : Set G}

namespace Exc

theorem key_special_special {a za b zb : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : Commute a b) (haza : Commute a za)
    (sa : za * b = b * za * a) (sb : zb * a = a * zb * b)
    (star : a * za * (b * zb) = b * zb * (a * za)) : za * zb = zb * a * za := by
  have L : a * za * (b * zb) = b * za * zb := by
    calc a * za * (b * zb) = a * (za * b) * zb := by simp only [mul_assoc]
      _ = a * (b * za * a) * zb := by rw [sa]
      _ = (a * b) * za * a * zb := by simp only [mul_assoc]
      _ = (b * a) * za * a * zb := by rw [hab.eq]
      _ = b * (a * za) * a * zb := by simp only [mul_assoc]
      _ = b * (za * a) * a * zb := by rw [haza.eq]
      _ = b * za * (a * a) * zb := by simp only [mul_assoc]
      _ = b * za * zb := by rw [ha, mul_one]
  have R : b * zb * (a * za) = b * (a * zb * b) * za := by
    calc b * zb * (a * za) = b * (zb * a) * za := by simp only [mul_assoc]
      _ = b * (a * zb * b) * za := by rw [sb]
  rw [L, R] at star
  have h1 : za * zb = a * zb * b * za := by
    have := congrArg (fun t => b * t) star
    simp only [← mul_assoc, hb, one_mul] at this
    simpa only [mul_assoc] using this
  rw [h1, ← sb]

end Exc

open Exc

theorem eq_of_special_special {u v c zu zv : G} (hu : u * u = 1) (hv : v * v = 1)
    (hc : c * c = 1) (hzu : zu * zu = 1) (hzv : zv * zv = 1) (huv : Commute u v)
    (hzuu : Commute u zu) (hzvv : Commute v zv) (hcu : c * u * c = u * zu)
    (hcv : c * v * c = v * zv) (h3 : (zu * v) ^ 2 = u) (h4 : (zv * u) ^ 2 = v) : u = v := by
  have h3' : zu * v * zu * v = u := by rw [← h3, pow_two]; simp only [mul_assoc]
  have h4' : zv * u * zv * u = v := by rw [← h4, pow_two]; simp only [mul_assoc]
  have t1 : v * zu * v = zu * u := by
    calc v * zu * v = zu * zu * (v * zu * v) := by rw [hzu, one_mul]
      _ = zu * (zu * v * zu * v) := by simp only [mul_assoc]
      _ = zu * u := by rw [h3']
  have t2 : u * zv * u = zv * v := by
    calc u * zv * u = zv * zv * (u * zv * u) := by rw [hzv, one_mul]
      _ = zv * (zv * u * zv * u) := by simp only [mul_assoc]
      _ = zv * v := by rw [h4']
  have s1 : zu * v = v * zu * u := by
    calc zu * v = v * v * (zu * v) := by rw [hv, one_mul]
      _ = v * (v * zu * v) := by simp only [mul_assoc]
      _ = v * zu * u := by rw [t1, ← mul_assoc]
  have s2 : zv * u = u * zv * v := by
    calc zv * u = u * u * (zv * u) := by rw [hu, one_mul]
      _ = u * (u * zv * u) := by simp only [mul_assoc]
      _ = u * zv * v := by rw [t2, ← mul_assoc]
  have star : u * zu * (v * zv) = v * zv * (u * zu) := by
    rw [← hcu, ← hcv]
    calc c * u * c * (c * v * c) = c * u * (c * c) * v * c := by simp only [mul_assoc]
      _ = c * (u * v) * c := by rw [hc, mul_one]; simp only [mul_assoc]
      _ = c * (v * u) * c := by rw [huv.eq]
      _ = c * v * (c * c) * u * c := by rw [hc, mul_one]; simp only [mul_assoc]
      _ = c * v * c * (c * u * c) := by simp only [mul_assoc]
  have P1 := key_special_special hu hv huv hzuu s1 s2 star
  have P2 := key_special_special hv hu huv.symm hzvv s2 s1 star.symm
  have P2' : zu * zv = zv * v * zu := by
    have := congrArg (fun t => t⁻¹) P2
    simp only [mul_inv_rev, inv_eq_of_mul_eq_one_right hzu, inv_eq_of_mul_eq_one_right hzv,
      inv_eq_of_mul_eq_one_right hv] at this
    simpa only [mul_assoc] using this
  rw [P1] at P2'
  exact mul_left_cancel (mul_right_cancel P2')

theorem not_commute_of_orderOf_eq_four {x c : G} (hx : x * x = 1) (hc : c * c = 1)
    (h4 : orderOf (x * c) = 4) : ¬ Commute x c := fun hxc => by
  have h := orderOf_dvd_of_pow_eq_one ((commute_iff_mul_sq_eq_one hx hc).1 hxc)
  rw [h4] at h
  exact absurd h (by norm_num)

theorem orderOf_sq_mul_eq_four (hD : IsRootInvolutionSet D) (hNP : NoPolar D)
    (hPl : ExcNoPlane D) {x y c : G} (hx : x ∈ D) (hy : y ∈ D) (hc : c ∈ D) (hxy : Commute x y)
    (hxyD : x * y ∈ D) (hx4 : orderOf (x * c) = 4) (hy4 : orderOf (y * c) = 4)
    (hxy4 : orderOf (x * y * c) = 4) (hxzD : x * (x * c) ^ 2 ∈ D) :
    orderOf ((x * c) ^ 2 * y) = 4 := by
  have hc2 := hD.mul_self_eq_one hc
  obtain ⟨hzD, hxz, hcz, -⟩ := sq_mem_of_orderOf_eq_four hD hx hc hx4
  have hz2 := hD.mul_self_eq_one hzD
  have hy2 := hD.mul_self_eq_one hy
  have hzc : Commute ((x * c) ^ 2) c := hcz.symm
  have hnx := not_commute_of_orderOf_eq_four (hD.mul_self_eq_one hx) hc2 hx4
  have hny := not_commute_of_orderOf_eq_four hy2 hc2 hy4
  have hnxy := not_commute_of_orderOf_eq_four (hD.mul_self_eq_one hxyD) hc2 hxy4
  have hzx : (x * c) ^ 2 ≠ x := fun e => hnx (e ▸ hzc)
  have hzy : (x * c) ^ 2 ≠ y := fun e => hny (e ▸ hzc)
  have hzxy : (x * c) ^ 2 ≠ x * y := fun e => hnxy (e ▸ hzc)
  rcases hD.orderOf_mul hzD hy with h | h | hodd
  ·
    exfalso
    have hzy' : Commute ((x * c) ^ 2) y := by
      refine (commute_iff_mul_sq_eq_one hz2 hy2).2 ?_
      have := pow_orderOf_eq_one ((x * c) ^ 2 * y)
      rwa [h] at this
    have hne_xy : x ≠ y := fun e => hD.ne_one hxyD (by rw [e, hy2])
    have hyzD : y * (x * c) ^ 2 ∈ D := hNP y hy _ hzD hzy'.symm (Ne.symm hzy)
    have hxyzD : x * y * (x * c) ^ 2 ∈ D := by
      rw [mul_assoc]
      refine hNP x hx _ hyzD (hxy.mul_right hxz) fun e => hzxy ?_
      calc (x * c) ^ 2 = y * (y * (x * c) ^ 2) := by rw [← mul_assoc, hy2, one_mul]
        _ = y * x := by rw [← e]
        _ = x * y := hxy.eq.symm
    exact hPl x hx y hy _ hzD hxy hxz hzy'.symm hne_xy hzx hzy hzxy hxyD hxzD hyzD hxyzD
  · exact h
  ·
    exfalso
    have e := eq_of_collinear_of_odd_of_mem hD hzD hx hxz.symm (by rw [← hxz.eq]; exact hxzD)
      hy hxy.symm (by rw [orderOf_mul_comm_eq]; exact hodd)
    exact hzy e.symm

theorem commute_of_special_special (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hsing : ∀ x ∈ D, rootSet D x = {x}) (hQ : CommLambda D)
    (hNP : NoPolar D) (hPl : ExcNoPlane D) {u v c : G} (hu : u ∈ D) (hv : v ∈ D) (hc : c ∈ D)
    (huv : Commute u v) (huvD : u * v ∈ D) (h1 : orderOf (u * c) = 4)
    (h2 : orderOf (v * c) = 4) : Commute (u * v) c := by
  have hconj : ∀ g x : G, x ∈ D → g * x * g⁻¹ ∈ D := fun g x hx => conj_mem_of_isClass hclass g hx
  have hu2 := hD.mul_self_eq_one hu
  have hv2 := hD.mul_self_eq_one hv
  have hc2 := hD.mul_self_eq_one hc
  by_contra hcomm
  have huvc : orderOf (u * v * c) = 4 := by
    rcases hD.orderOf_mul huvD hc with h | h | hodd
    · exact absurd ((commute_iff_mul_sq_eq_one (hD.mul_self_eq_one huvD) hc2).2
        (h ▸ pow_orderOf_eq_one _)) hcomm
    · exact h
    · exfalso
      refine Closure.not_special_special_of_opposite hclass hD huvD hu
        ((Commute.refl u).mul_left huv.symm) hc hcomm hodd ?_ ?_
      · rw [orderOf_mul_comm_eq]; exact h1
      · rw [show u * v * u = v by rw [huv.eq, mul_assoc, hu2, mul_one], orderOf_mul_comm_eq]
        exact h2
  have hvuD : v * u ∈ D := by rw [← huv.eq]; exact huvD
  have hvuc : orderOf (v * u * c) = 4 := by rw [← huv.eq]; exact huvc
  obtain ⟨hzuD, hzu_u, -, hcu⟩ := sq_mem_of_orderOf_eq_four hD hu hc h1
  obtain ⟨hzvD, hzv_v, -, hcv⟩ := sq_mem_of_orderOf_eq_four hD hv hc h2
  have huzuD : u * (u * c) ^ 2 ∈ D := by
    rw [← hcu]; simpa [hD.inv_eq hc] using hconj c u hu
  have hvzvD : v * (v * c) ^ 2 ∈ D := by
    rw [← hcv]; simpa [hD.inv_eq hc] using hconj c v hv
  have h3 : ((u * c) ^ 2 * v) ^ 2 = u := by
    have := hQ u hu _ hzuD v hv hzu_u huzuD huv huvD
      (orderOf_sq_mul_eq_four hD hNP hPl hu hv hc huv huvD h1 h2 huvc huzuD)
    rwa [hsing u hu, Set.mem_singleton_iff] at this
  have h4 : ((v * c) ^ 2 * u) ^ 2 = v := by
    have := hQ v hv _ hzvD u hu hzv_v hvzvD huv.symm hvuD
      (orderOf_sq_mul_eq_four hD hNP hPl hv hu hc huv.symm hvuD h2 h1 hvuc hvzvD)
    rwa [hsing v hv, Set.mem_singleton_iff] at this
  have heq := eq_of_special_special hu2 hv2 hc2 (hD.mul_self_eq_one hzuD)
    (hD.mul_self_eq_one hzvD) huv hzu_u hzv_v hcu hcv h3 h4
  exact hD.ne_one huvD (by rw [heq, hv2])

end CFSG.Timmesfeld.Moufang
