module

public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup

private theorem w85g_eq_one_of_mul_self_eq_one_of_odd {Y : Type} [Group Y] {N : Subgroup Y}
    (hN : Odd (Nat.card N)) {δ : Y} (hδ : δ ∈ N) (h : δ * δ = 1) : δ = 1 := by
  have h2 : orderOf δ ∣ 2 := by
    rw [← pow_two] at h
    exact orderOf_dvd_of_pow_eq_one h
  have hcard : orderOf δ ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hδ
  have hcop : Nat.Coprime 2 (Nat.card N) := hN.coprime_two_right.symm
  have hone : orderOf δ = 1 := Nat.eq_one_of_dvd_coprimes hcop h2 hcard
  exact orderOf_eq_one_iff.mp hone

theorem gap5Grp_eq_one_of_fixes_normal_odd {Y : Type} [Group Y] [Finite Y] {N : Subgroup Y}
    [N.Normal] (hN : Odd (Nat.card N)) (hC : Subgroup.centralizer (N : Set Y) ≤ N)
    {b : MulAut Y} (hb2 : b * b = 1) (hbN : ∀ o ∈ N, b o = o) : b = 1 := by
  ext k
  change b k = k
  let δ : Y := k⁻¹ * b k
  have hδC : δ ∈ Subgroup.centralizer (N : Set Y) := by
    change k⁻¹ * b k ∈ Subgroup.centralizer (N : Set Y)
    rw [Subgroup.mem_centralizer_iff]
    intro o ho
    have hconj : k * o * k⁻¹ ∈ N := (inferInstance : N.Normal).conj_mem o ho k
    have hbconj : b (k * o * k⁻¹) = k * o * k⁻¹ := hbN _ hconj
    simp only [map_mul, map_inv, hbN o ho] at hbconj
    have h1 : k * o * k⁻¹ * b k = b k * o :=
      (mul_inv_eq_iff_eq_mul.mp hbconj).symm
    have hcomm : o * (k⁻¹ * b k) = (k⁻¹ * b k) * o := by
      apply mul_left_cancel (a := k)
      calc
        k * (o * (k⁻¹ * b k)) = k * o * k⁻¹ * b k := by simp only [mul_assoc]
        _ = b k * o := h1
        _ = k * ((k⁻¹ * b k) * o) := by rw [← mul_assoc, mul_inv_cancel_left]
    exact hcomm
  have hδN : δ ∈ N := hC hδC
  have hbδ : b δ = δ := hbN δ hδN
  have hbk : b k = k * δ := by
    change b k = k * (k⁻¹ * b k)
    exact (mul_inv_cancel_left k (b k)).symm
  have hb2k : b (b k) = k := by
    have h := congrArg (fun e : MulAut Y => e k) hb2
    simpa [MulAut.mul_apply, MulAut.one_apply] using h
  have hδ2 : δ * δ = 1 := by
    have hkey : k = k * (δ * δ) := by
      calc
        k = b (b k) := hb2k.symm
        _ = b (k * δ) := by rw [← hbk]
        _ = b k * b δ := by rw [map_mul]
        _ = (k * δ) * δ := by rw [hbk, hbδ]
        _ = k * (δ * δ) := by rw [mul_assoc]
    have hkey' : k * 1 = k * (δ * δ) := by
      rw [mul_one]
      exact hkey
    exact (mul_left_cancel hkey').symm
  have hδ1 : δ = 1 := w85g_eq_one_of_mul_self_eq_one_of_odd hN hδN hδ2
  rw [hbk, hδ1, mul_one]

theorem gap5Grp_mem_centralizer_of_involution {Y : Type} [Group Y] [Finite Y] {N : Subgroup Y}
    [N.Normal] (hN : Odd (Nat.card N)) {t c : Y} (ht : t * t = 1)
    (hc : c ∈ Subgroup.centralizer (N : Set Y))
    (h0 : (t * (c * t * c⁻¹)) * (t * (c * t * c⁻¹)) = 1)
    (hq : ∀ q ∈ N, (t * (q * (c * t * c⁻¹) * q⁻¹)) * (t * (q * (c * t * c⁻¹) * q⁻¹)) = 1) :
    t ∈ Subgroup.centralizer (N : Set Y) := by
  rw [Subgroup.mem_centralizer_iff]
  intro q hqN
  let t' : Y := c * t * c⁻¹
  let g : Y := t * t'
  let w : Y := q * t * q⁻¹ * t
  let w'' : Y := t * w * t
  have ht_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hc' : c⁻¹ ∈ Subgroup.centralizer (N : Set Y) := (Subgroup.centralizer (N : Set Y)).inv_mem hc
  have hcN : ∀ m ∈ N, m * c = c * m :=
    fun m hm => Subgroup.mem_centralizer_iff.mp hc m hm
  have hcN' : ∀ m ∈ N, m * c⁻¹ = c⁻¹ * m :=
    fun m hm => Subgroup.mem_centralizer_iff.mp hc' m hm
  have htnt : ∀ m ∈ N, t * m * t ∈ N := by
    intro m hm
    simpa [ht_inv] using (inferInstance : N.Normal).conj_mem m hm t
  have h0' : g * g = 1 := h0
  have hq' : ∀ q ∈ N, (t * (q * t' * q⁻¹)) * (t * (q * t' * q⁻¹)) = 1 :=
    fun q hqN => hq q hqN
  have hA : t * c * t ∈ Subgroup.centralizer (N : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    have hn' : t * n * t ∈ N := htnt n hn
    have hn'c : (t * n * t) * c = c * (t * n * t) := hcN _ hn'
    have hAinv : (t * c * t)⁻¹ = t * c⁻¹ * t := by
      rw [mul_inv_rev, mul_inv_rev, ht_inv, mul_assoc]
    have hconj : (t * c * t) * n * (t * c * t)⁻¹ = n := by
      rw [hAinv]
      calc
        (t * c * t) * n * (t * c⁻¹ * t)
            = t * (c * (t * n * t)) * c⁻¹ * t := by simp only [mul_assoc]
        _ = t * ((t * n * t) * c) * c⁻¹ * t := by rw [← hn'c]
        _ = t * (t * n * t) * t := by
              simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel_right, mul_one]
        _ = n := by
              calc
                t * (t * n * t) * t = (t * t) * n * (t * t) := by simp only [mul_assoc]
                _ = 1 * n * 1 := by rw [ht]
                _ = n := by rw [one_mul, mul_one]
    exact (mul_inv_eq_iff_eq_mul.mp hconj).symm
  have hg : g ∈ Subgroup.centralizer (N : Set Y) := by
    have hmem : (t * c * t) * c⁻¹ ∈ Subgroup.centralizer (N : Set Y) :=
      (Subgroup.centralizer (N : Set Y)).mul_mem hA hc'
    have heq : g = (t * c * t) * c⁻¹ := by
      show t * (c * t * c⁻¹) = (t * c * t) * c⁻¹
      simp only [mul_assoc]
    rwa [heq]
  have hwN : w ∈ N := by
    show q * t * q⁻¹ * t ∈ N
    have hqinv : q⁻¹ ∈ N := N.inv_mem hqN
    have htq : t * q⁻¹ * t ∈ N := htnt q⁻¹ hqinv
    have hmem : q * (t * q⁻¹ * t) ∈ N := N.mul_mem hqN htq
    simpa only [mul_assoc] using hmem
  have hw''N : w'' ∈ N := by
    show t * w * t ∈ N
    exact htnt w hwN
  have hqtw : q * t * q⁻¹ = w * t := by
    show q * t * q⁻¹ = (q * t * q⁻¹ * t) * t
    simp only [mul_assoc, ht, mul_one]
  have hqt' : q * t' * q⁻¹ = w * t' := by
    show q * (c * t * c⁻¹) * q⁻¹ = (q * t * q⁻¹ * t) * (c * t * c⁻¹)
    have hqc : q * c = c * q := hcN q hqN
    have hqinv : q⁻¹ ∈ N := N.inv_mem hqN
    have hqic' : q⁻¹ * c⁻¹ = c⁻¹ * q⁻¹ := hcN' q⁻¹ hqinv
    have hwc : w * c = c * w := hcN w hwN
    calc
      q * (c * t * c⁻¹) * q⁻¹ = q * c * t * c⁻¹ * q⁻¹ := by simp only [mul_assoc]
      _ = c * q * t * c⁻¹ * q⁻¹ := by rw [hqc]
      _ = c * q * t * (c⁻¹ * q⁻¹) := by simp only [mul_assoc]
      _ = c * q * t * (q⁻¹ * c⁻¹) := by rw [← hqic']
      _ = c * (q * t * q⁻¹) * c⁻¹ := by simp only [mul_assoc]
      _ = c * (w * t) * c⁻¹ := by rw [hqtw]
      _ = (q * t * q⁻¹ * t) * (c * t * c⁻¹) := by
            show c * (w * t) * c⁻¹ = w * (c * t * c⁻¹)
            calc
              c * (w * t) * c⁻¹ = c * w * t * c⁻¹ := by simp only [mul_assoc]
              _ = w * c * t * c⁻¹ := by rw [← hwc]
              _ = w * (c * t * c⁻¹) := by simp only [mul_assoc]
  have hcancel : (t * w * t) * (t * t') = t * w * t' := by
    calc
      (t * w * t) * (t * t') = t * w * (t * t) * t' := by simp only [mul_assoc]
      _ = t * w * 1 * t' := by rw [ht]
      _ = t * w * t' := by simp only [mul_one]
  have htq' : t * (q * t' * q⁻¹) = w'' * g := by
    show t * (q * t' * q⁻¹) = (t * w * t) * (t * t')
    rw [hqt']
    simpa only [mul_assoc] using hcancel.symm
  have hsq : (w'' * g) * (w'' * g) = 1 := by
    have h := hq' q hqN
    rwa [htq'] at h
  have hgw : w'' * g = g * w'' := Subgroup.mem_centralizer_iff.mp hg w'' hw''N
  have hsq' : w'' * w'' = 1 := by
    have h1 : (w'' * g) * (w'' * g) = w'' * w'' * (g * g) := by
      calc
        (w'' * g) * (w'' * g) = w'' * (g * (w'' * g)) := by simp only [mul_assoc]
        _ = w'' * ((g * w'') * g) := by simp only [mul_assoc]
        _ = w'' * ((w'' * g) * g) := by rw [← hgw]
        _ = w'' * w'' * (g * g) := by simp only [mul_assoc]
    have h2 : w'' * w'' * (g * g) = 1 := by rw [← h1]; exact hsq
    rwa [h0', mul_one] at h2
  have hw''1 : w'' = 1 := w85g_eq_one_of_mul_self_eq_one_of_odd hN hw''N hsq'
  have htw''t : t * w'' * t = w := by
    show t * (t * w * t) * t = w
    calc
      t * (t * w * t) * t = (t * t) * w * (t * t) := by simp only [mul_assoc]
      _ = 1 * w * 1 := by rw [ht]
      _ = w := by rw [one_mul, mul_one]
  have hw1 : w = 1 := by
    rw [← htw''t, hw''1, mul_one, ht]
  have hqt : q * t * q⁻¹ = t := by rw [hqtw, hw1, one_mul]
  calc
    q * t = (q * t * q⁻¹) * q := (inv_mul_cancel_right (q * t) q).symm
    _ = t * q := by rw [hqt]

theorem gap5Grp_eq_one_of_central_odd_kernel {X Y : Type} [Group X] [Finite X] [Group Y]
    (ψ : X →* Y) (hZ : ψ.ker ≤ Subgroup.center X) (hodd : Odd (Nat.card ψ.ker))
    (hgen : Subgroup.closure {x : X | x * x = 1} = ⊤) {a : MulAut X} (ha : ∀ x, ψ (a x) = ψ x) :
    a = 1 := by
  have hax : ∀ x : X, x * x = 1 → a x = x := by
    intro x hx
    let z : X := x⁻¹ * a x
    have hzmem : z ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      show ψ (x⁻¹ * a x) = 1
      rw [map_mul, map_inv, ha x, inv_mul_cancel]
    have hzcenter : z ∈ Subgroup.center X := hZ hzmem
    have haz : a x = x * z := by
      show a x = x * (x⁻¹ * a x)
      rw [mul_inv_cancel_left]
    have hx2 : a x * a x = 1 := by
      have h := map_mul a x x
      simp only [hx, map_one] at h
      exact h.symm
    have hzx : z * x = x * z := (Subgroup.mem_center_iff.mp hzcenter x).symm
    have hxz : (x * z) * (x * z) = z * z := by
      calc
        (x * z) * (x * z) = ((x * z) * x) * z := by rw [← mul_assoc]
        _ = (x * (z * x)) * z := by rw [mul_assoc x z x]
        _ = (x * (x * z)) * z := by rw [hzx]
        _ = ((x * x) * z) * z := by rw [← mul_assoc x x z]
        _ = (x * x) * (z * z) := by rw [mul_assoc (x * x) z z]
        _ = z * z := by rw [hx, one_mul]
    have hz2 : z * z = 1 := by
      rw [← hxz, ← haz, hx2]
    have hz1 : z = 1 := w85g_eq_one_of_mul_self_eq_one_of_odd hodd hzmem hz2
    rw [haz, hz1, mul_one]
  ext y
  change a y = y
  have hgen' : y ∈ Subgroup.closure {x : X | x * x = 1} := by
    rw [hgen]
    exact Subgroup.mem_top y
  have heqon : Set.EqOn a.toMonoidHom (MonoidHom.id X) {x : X | x * x = 1} := by
    intro x hx
    simpa using hax x hx
  have hy := MonoidHom.eqOn_closure heqon hgen'
  simpa using hy

end CFSG.LocalAnalysis.WeakClosure81

end
