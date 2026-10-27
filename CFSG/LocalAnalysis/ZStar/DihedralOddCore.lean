module

public import CFSG.LocalAnalysis.ZStar.DihedralCentralizer

public section

namespace CFSG

namespace ZStar.DihedralOddCore

open ZStar.DihedralCentralizer

universe u

private theorem odd_orderOf_of_mem_odd_subgroup
    {Y : Type u} [Group Y] (N : Subgroup Y)
    (hNodd : Odd (Nat.card N)) {y : Y} (hy : y ∈ N) :
    Odd (orderOf y) :=
  hNodd.of_dvd_nat (N.orderOf_dvd_natCard hy)

private theorem square_mem_of_commutator_witness
    {Y : Type u} [Group Y] {t h : Y}
    (ht2 : t * t = 1) (hh2 : h * h = 1)
    (N : Subgroup Y)
    (hcomm : ∀ g : Y, g * t * g⁻¹ * t⁻¹ ∈ N) :
    (t * h) ^ 2 ∈ N := by
  have ht_inv : t⁻¹ = t := (inv_eq_iff_mul_eq_one).2 ht2
  have hh_inv : h⁻¹ = h := (inv_eq_iff_mul_eq_one).2 hh2
  have hmem := hcomm (t * h)
  have heq : (t * h) * t * (t * h)⁻¹ * t⁻¹ = (t * h) ^ 2 := by
    calc
      (t * h) * t * (t * h)⁻¹ * t⁻¹ =
          (t * h) * t * (h * t) * t := by
            rw [mul_inv_rev, ht_inv, hh_inv]
      _ = (t * h) * (t * h) * (t * t) := by group
      _ = (t * h) * (t * h) := by rw [ht2, mul_one]
      _ = (t * h) ^ 2 := by rw [pow_two]
  rw [heq] at hmem
  exact hmem

theorem dihedral_oddCore_package
    {Y : Type u} [Group Y] [Fintype Y] {t h : Y}
    (ht2 : t * t = 1) (hh2 : h * h = 1)
    (heven : Even (orderOf (t * h)))
    (N : Subgroup Y) (hNodd : Odd (Nat.card N))
    (hcomm : ∀ g : Y, g * t * g⁻¹ * t⁻¹ ∈ N) :
    let x := t * h
    let n := orderOf x / 2
    let w := x ^ n
    let v := w * x
    let μ := t * w
    x ^ 2 ∈ N ∧ Odd (orderOf (x ^ 2)) ∧ Odd n ∧
      v = x ^ (n + 1) ∧ v ∈ N ∧
      μ * μ = 1 ∧ μ * h = v ∧ μ * h ∈ N ∧
      Odd (orderOf (μ * h)) ∧ IsConj μ h := by
  let x : Y := t * h
  let n : ℕ := orderOf x / 2
  let w : Y := x ^ n
  let v : Y := w * x
  let μ : Y := t * w
  change x ^ 2 ∈ N ∧ Odd (orderOf (x ^ 2)) ∧ Odd n ∧
    v = x ^ (n + 1) ∧ v ∈ N ∧
    μ * μ = 1 ∧ μ * h = v ∧ μ * h ∈ N ∧
    Odd (orderOf (μ * h)) ∧ IsConj μ h
  have hx2N : x ^ 2 ∈ N := by
    simpa only [x] using
      square_mem_of_commutator_witness ht2 hh2 N hcomm
  have hx2odd : Odd (orderOf (x ^ 2)) :=
    odd_orderOf_of_mem_odd_subgroup N hNodd hx2N
  have hevenx : Even (orderOf x) := by
    simpa only [x] using heven
  have horder_x2 : orderOf (x ^ 2) = n := by
    calc
      orderOf (x ^ 2) = orderOf x / 2 :=
        orderOf_pow_of_dvd (by norm_num) (even_iff_two_dvd.mp hevenx)
      _ = n := rfl
  have hnodd : Odd n := by
    rw [← horder_x2]
    exact hx2odd
  have hwdata :
      w ≠ 1 ∧ w * w = 1 ∧ Commute t w ∧ Commute h w := by
    simpa only [x, n, w] using halfOrder_involution ht2 hh2 heven
  obtain ⟨_hw1, hw2, htw, _hhw⟩ := hwdata
  have hvpow : v = x ^ (n + 1) := by
    calc
      v = x ^ n * x := rfl
      _ = x ^ (n + 1) := (pow_succ x n).symm
  obtain ⟨k, hk⟩ := hnodd
  have hv_sqpow : v = (x ^ 2) ^ (k + 1) := by
    calc
      v = x ^ (n + 1) := hvpow
      _ = x ^ (2 * (k + 1)) := by
        congr 1
        omega
      _ = (x ^ 2) ^ (k + 1) := pow_mul x 2 (k + 1)
  have hvN : v ∈ N := by
    rw [hv_sqpow]
    exact N.pow_mem hx2N (k + 1)
  have hmu2 : μ * μ = 1 := by
    calc
      μ * μ = (t * w) * (t * w) := rfl
      _ = t * (w * t) * w := by group
      _ = t * (t * w) * w := by rw [← htw.eq]
      _ = (t * t) * (w * w) := by group
      _ = 1 := by rw [ht2, hw2, one_mul]
  have hmuhv : μ * h = v := by
    calc
      μ * h = (t * w) * h := rfl
      _ = (w * t) * h := by rw [htw.eq]
      _ = w * (t * h) := by rw [mul_assoc]
      _ = v := rfl
  have hmuhN : μ * h ∈ N := by
    rw [hmuhv]
    exact hvN
  have hmuhodd : Odd (orderOf (μ * h)) :=
    odd_orderOf_of_mem_odd_subgroup N hNodd hmuhN
  have hconj : IsConj μ h :=
    isConj_of_involutions_odd_product hmu2 hh2 hmuhodd
  exact ⟨hx2N, hx2odd, ⟨k, hk⟩, hvpow, hvN, hmu2, hmuhv,
    hmuhN, hmuhodd, hconj⟩

end ZStar.DihedralOddCore

end CFSG
