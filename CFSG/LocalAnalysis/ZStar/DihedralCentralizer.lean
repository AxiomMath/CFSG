module

public import CFSG.LocalAnalysis.ZStar.CentralizerInduction

public section

namespace CFSG

namespace ZStar.DihedralCentralizer

open ZStar.TransferReduction ZStar.CentralizerInduction

universe u

noncomputable local instance subgroupFintype
    {X : Type u} [Group X] [Fintype X] (H : Subgroup X) : Fintype H :=
  Fintype.ofFinite H

theorem isConj_of_involutions_odd_product
    {X : Type u} [Group X] {a b : X}
    (ha2 : a * a = 1) (hb2 : b * b = 1)
    (hodd : Odd (orderOf (a * b))) :
    IsConj a b := by
  let x : X := a * b
  have ha_inv : a⁻¹ = a := (inv_eq_iff_mul_eq_one).2 ha2
  have hb_inv : b⁻¹ = b := (inv_eq_iff_mul_eq_one).2 hb2
  have hax : SemiconjBy a x x⁻¹ := by
    change a * (a * b) = (a * b)⁻¹ * a
    calc
      a * (a * b) = (a * a) * b := by rw [mul_assoc]
      _ = b := by rw [ha2, one_mul]
      _ = b * (a * a) := by rw [ha2, mul_one]
      _ = (b * a) * a := by rw [mul_assoc]
      _ = (a * b)⁻¹ * a := by rw [mul_inv_rev, ha_inv, hb_inv]
  have hax_inv : SemiconjBy a x⁻¹ x := by
    simpa using hax.inv_right
  obtain ⟨k, hk⟩ := hodd
  have hxorder : orderOf x = 2 * k + 1 := by
    simpa [x] using hk
  have hcomplement : (x ^ k)⁻¹ = x ^ (k + 1) := by
    apply (inv_eq_iff_mul_eq_one).2
    rw [← pow_add, show k + (k + 1) = orderOf x by omega]
    exact pow_orderOf_eq_one x
  have hax_eq_b : a * x = b := by
    simp only [x, ← mul_assoc, ha2, one_mul]
  have hsemi : x ^ k * a = b * x ^ k := by
    calc
      x ^ k * a = a * (x⁻¹) ^ k := (hax_inv.pow_right k).eq.symm
      _ = a * x ^ (k + 1) := by rw [inv_pow, hcomplement]
      _ = a * (x * x ^ k) := by rw [pow_succ']
      _ = (a * x) * x ^ k := (mul_assoc _ _ _).symm
      _ = b * x ^ k := by rw [hax_eq_b]
  rw [isConj_iff]
  refine ⟨x ^ k, ?_⟩
  calc
    x ^ k * a * (x ^ k)⁻¹ = (b * x ^ k) * (x ^ k)⁻¹ := by rw [hsemi]
    _ = b := by rw [mul_assoc, mul_inv_cancel, mul_one]

theorem halfOrder_involution
    {X : Type u} [Group X] [Fintype X] {t h : X}
    (ht2 : t * t = 1) (hh2 : h * h = 1)
    (heven : Even (orderOf (t * h))) :
    let n := orderOf (t * h) / 2
    let w := (t * h) ^ n
    w ≠ 1 ∧ w * w = 1 ∧ Commute t w ∧ Commute h w := by
  let x : X := t * h
  let n : ℕ := orderOf x / 2
  let w : X := x ^ n
  change w ≠ 1 ∧ w * w = 1 ∧ Commute t w ∧ Commute h w
  have hevenx : Even (orderOf x) := by
    simpa [x] using heven
  have hdouble : 2 * n = orderOf x := by
    simpa [n] using Nat.two_mul_div_two_of_even hevenx
  have horder_pos : 0 < orderOf x :=
    (isOfFinOrder_of_finite x).orderOf_pos
  have hn_pos : 0 < n := by omega
  have hn_lt : n < orderOf x := by omega
  have hw1 : w ≠ 1 := by
    exact pow_ne_one_of_lt_orderOf (Nat.ne_of_gt hn_pos) hn_lt
  have hw2 : w * w = 1 := by
    calc
      w * w = x ^ n * x ^ n := rfl
      _ = x ^ (n + n) := (pow_add x n n).symm
      _ = x ^ orderOf x := by
        congr 1
        omega
      _ = 1 := pow_orderOf_eq_one x
  have hw_inv : w⁻¹ = w := (inv_eq_iff_mul_eq_one).2 hw2
  have ht_inv : t⁻¹ = t := (inv_eq_iff_mul_eq_one).2 ht2
  have hh_inv : h⁻¹ = h := (inv_eq_iff_mul_eq_one).2 hh2
  have htx : SemiconjBy t x x⁻¹ := by
    change t * (t * h) = (t * h)⁻¹ * t
    calc
      t * (t * h) = (t * t) * h := by rw [mul_assoc]
      _ = h := by rw [ht2, one_mul]
      _ = h * (t * t) := by rw [ht2, mul_one]
      _ = (h * t) * t := by rw [mul_assoc]
      _ = (t * h)⁻¹ * t := by rw [mul_inv_rev, ht_inv, hh_inv]
  have hhx : SemiconjBy h x x⁻¹ := by
    change h * (t * h) = (t * h)⁻¹ * h
    calc
      h * (t * h) = (h * t) * h := (mul_assoc _ _ _).symm
      _ = (t * h)⁻¹ * h := by rw [mul_inv_rev, ht_inv, hh_inv]
  have hinvpow : (x⁻¹) ^ n = w := by
    rw [inv_pow]
    exact hw_inv
  have htw : Commute t w := by
    calc
      t * w = (x⁻¹) ^ n * t := (htx.pow_right n).eq
      _ = w * t := by rw [hinvpow]
  have hhw : Commute h w := by
    calc
      h * w = (x⁻¹) ^ n * h := (hhx.pow_right n).eq
      _ = w * h := by rw [hinvpow]
  exact ⟨hw1, hw2, htw, hhw⟩

theorem dihedral_centralizer_induction_or_zStar
    {X : Type u} [Group X] [Fintype X] {t h : X}
    (ht : Isolated t) (ht2 : t * t = 1) (hh2 : h * h = 1)
    (hmin : ∀ H : Subgroup X, H.Normal → t ∈ H → H = ⊤)
    (ih :
      ∀ {Y : Type u} [Group Y] [Fintype Y] {y : Y},
        Nat.card Y < Nat.card X → Isolated y → y * y = 1 →
          ZStarConclusion Y y)
    (heven : Even (orderOf (t * h))) :
    let w := (t * h) ^ (orderOf (t * h) / 2)
    ZStarConclusion X t ∨
      ∃ (H : Subgroup X) (htH : t ∈ H) (_hhH : h ∈ H) (_hwH : w ∈ H),
        H = Subgroup.centralizer ({w} : Set X) ∧ H ≠ ⊤ ∧
        Nat.card H < Nat.card X ∧
        Isolated (⟨t, htH⟩ : H) ∧
        (⟨t, htH⟩ : H) * ⟨t, htH⟩ = 1 ∧
        ZStarConclusion H (⟨t, htH⟩ : H) := by
  let w : X := (t * h) ^ (orderOf (t * h) / 2)
  change ZStarConclusion X t ∨
    ∃ (H : Subgroup X) (htH : t ∈ H) (_hhH : h ∈ H) (_hwH : w ∈ H),
      H = Subgroup.centralizer ({w} : Set X) ∧ H ≠ ⊤ ∧
      Nat.card H < Nat.card X ∧
      Isolated (⟨t, htH⟩ : H) ∧
      (⟨t, htH⟩ : H) * ⟨t, htH⟩ = 1 ∧
      ZStarConclusion H (⟨t, htH⟩ : H)
  have hwdata : w ≠ 1 ∧ w * w = 1 ∧ Commute t w ∧ Commute h w := by
    simpa only [w] using halfOrder_involution ht2 hh2 heven
  obtain ⟨hw1, hw2, htw, hhw⟩ := hwdata
  obtain hZ | ⟨H, htH, hH, hHne, hcard, hisolatedH, htH2, hih⟩ :=
    centralizer_induction_or_zStar ht ht2 hmin ih hw1 hw2 htw
  · exact Or.inl hZ
  · right
    have hhH : h ∈ H := by
      rw [hH, Subgroup.mem_centralizer_singleton_iff]
      exact hhw.eq
    have hwH : w ∈ H := by
      rw [hH, Subgroup.mem_centralizer_singleton_iff]
    exact ⟨H, htH, hhH, hwH, hH, hHne, hcard, hisolatedH, htH2, hih⟩

end ZStar.DihedralCentralizer

end CFSG
