module

public import CFSG.Monster.GMS.S365Basic
import CFSG.Monster.GMS.NotConj

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

namespace S365

variable {G : Type} [Group G] {d₀ : B} {a z₀ x y t : G}

theorem isConj_a_mul_of_mem
    [Finite G] (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) {w c : G}
    (hw : IsConj z₀ w) (hc : IsConj a c) (hcomm : c * w = w * c) (hQ : c ∈ leechQ w) :
    IsConj a (w * c) := by
  have hww : w * w = 1 :=
    mul_self_eq_one_of_orderOf ((orderOf_eq_of_isConj hw).symm.trans hG.2.1)
  have hcc : c * c = 1 := sq_of_isConj_a hG.1.1 hc
  have hwc2 : w * c * (w * c) = 1 := mul_mul_self_eq_one hww hcc hcomm.symm
  have hwc1 : w * c ≠ 1 := by
    intro h1
    have h2 : w = c⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [inv_eq_of_mul_eq_one_right hcc] at h2
    rw [h2] at hw
    exact hG.not_isConj (hc.trans hw.symm)
  rcases s31_five I.sls I.tableV I.leech hG I.leechInv
    (orderOf_eq_two_of_mul_self hwc2 hwc1) with hA | hB
  · exact hA
  · exact absurd hQ ((isConj_mul_iff I hG hw hc hcomm).1 hB)

theorem mul_mem_cosetSet {x y t w c : G} (h : IsKlein x y) (hw : w ∈ cosetSet x y t)
    (hc : InKlein x y c) : w * c ∈ cosetSet x y t := by
  obtain ⟨c₀, hc₀, rfl⟩ := mem_cosetSet_iff.1 hw
  exact mem_cosetSet_iff.2 ⟨c₀ * c, h.mul_mem hc₀ hc, by rw [mul_assoc]⟩

theorem klein_flag_cases {x y : G} (h : IsKlein x y) (S : Subgroup G) :
    (x ∈ S ∧ y ∈ S ∧ x * y ∈ S) ∨ (x ∈ S ∧ y ∉ S ∧ x * y ∉ S) ∨
      (x ∉ S ∧ y ∈ S ∧ x * y ∉ S) ∨ (x ∉ S ∧ y ∉ S ∧ x * y ∈ S) ∨
      (x ∉ S ∧ y ∉ S ∧ x * y ∉ S) := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right h.sq_x
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right h.sq_y
  by_cases hx : x ∈ S <;> by_cases hy : y ∈ S <;> by_cases hxy : x * y ∈ S
  · exact Or.inl ⟨hx, hy, hxy⟩
  · exact absurd (S.mul_mem hx hy) hxy
  · exact absurd (by
      have := S.mul_mem (S.inv_mem hx) hxy
      rwa [hxi, ← mul_assoc, h.sq_x, one_mul] at this) hy
  · exact Or.inr (Or.inl ⟨hx, hy, hxy⟩)
  · exact absurd (by
      have := S.mul_mem hxy (S.inv_mem hy)
      rwa [hyi, mul_assoc, h.sq_y, mul_one] at this) hx
  · exact Or.inr (Or.inr (Or.inl ⟨hx, hy, hxy⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hx, hy, hxy⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hx, hy, hxy⟩)))

theorem IsKlein.rel {x y : G} (h : IsKlein x y) :
    x * (x * y) = y ∧ y * (x * y) = x ∧ x * y * x = y ∧ x * y * y = x := by
  obtain ⟨hx, hy, hxy⟩ := h
  refine ⟨by rw [← mul_assoc, hx, one_mul], ?_, by rw [hxy, mul_assoc, hx, mul_one],
    by rw [mul_assoc, hy, mul_one]⟩
  rw [← mul_assoc, ← hxy, mul_assoc, hy, mul_one]

theorem exists_pivot_one
    [Finite G] (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hl : IsLineTriple a x y) (he : IsEightExt x y t) (hc : twoBCount z₀ x y t = 1) :
    ∃ w, IsConj z₀ w ∧ w ∈ cosetSet x y t ∧ x * w = w * x ∧ y * w = w * y ∧
      x ∈ leechQ w ∧ y ∈ leechQ w := by
  classical
  obtain ⟨w, hw, hwc⟩ := exists_twoB_mem_cosetSet I hG hl he
  have hK := isKlein_of_isLineTriple hG.1.1 hl
  obtain ⟨hxw, hyw⟩ := commute_of_mem_cosetSet hK.comm he.2.1 he.2.2.1 hwc
  rw [← twoBCount_eq_of_mem_cosetSet hK hwc,
    twoBCount_eq_of_twoB I hG hl hw hxw.symm hyw.symm] at hc
  refine ⟨w, hw, hwc, hxw.symm, hyw.symm, ?_⟩
  rcases klein_flag_cases hK (leechQ w) with ⟨hx, hy, hxy⟩ | ⟨hx, hy, hxy⟩ | ⟨hx, hy, hxy⟩ |
    ⟨hx, hy, hxy⟩ | ⟨hx, hy, hxy⟩ <;> simp [hx, hy, hxy] at hc ⊢

theorem exists_pivot_four
    [Finite G] (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hl : IsLineTriple a x y) (he : IsEightExt x y t) (hc : twoBCount z₀ x y t = 4) :
    ∃ w, IsConj z₀ w ∧ w ∈ cosetSet x y t ∧ x * w = w * x ∧ y * w = w * y ∧
      x ∉ leechQ w ∧ y ∉ leechQ w ∧ x * y ∉ leechQ w := by
  classical
  obtain ⟨w, hw, hwc⟩ := exists_twoB_mem_cosetSet I hG hl he
  have hK := isKlein_of_isLineTriple hG.1.1 hl
  obtain ⟨hxw, hyw⟩ := commute_of_mem_cosetSet hK.comm he.2.1 he.2.2.1 hwc
  rw [← twoBCount_eq_of_mem_cosetSet hK hwc,
    twoBCount_eq_of_twoB I hG hl hw hxw.symm hyw.symm] at hc
  refine ⟨w, hw, hwc, hxw.symm, hyw.symm, ?_⟩
  rcases klein_flag_cases hK (leechQ w) with ⟨hx, hy, hxy⟩ | ⟨hx, hy, hxy⟩ | ⟨hx, hy, hxy⟩ |
    ⟨hx, hy, hxy⟩ | ⟨hx, hy, hxy⟩ <;> simp [hx, hy, hxy] at hc ⊢

theorem exists_pivot_three
    [Finite G] (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hl : IsLineTriple a x y) (he : IsEightExt x y t) (hc : twoBCount z₀ x y t = 3) :
    ∃ w, IsConj z₀ w ∧ w ∈ cosetSet x y t ∧ x * w = w * x ∧ y * w = w * y ∧
      x ∈ leechQ w ∧ y ∉ leechQ w := by
  classical
  obtain ⟨w₀, hw₀, hwc⟩ := exists_twoB_mem_cosetSet I hG hl he
  have hK := isKlein_of_isLineTriple hG.1.1 hl
  obtain ⟨hxw, hyw⟩ := commute_of_mem_cosetSet hK.comm he.2.1 he.2.2.1 hwc
  rw [← twoBCount_eq_of_mem_cosetSet hK hwc,
    twoBCount_eq_of_twoB I hG hl hw₀ hxw.symm hyw.symm] at hc
  obtain ⟨hxA, hyA, hxyA⟩ := hl
  obtain ⟨r1, r2, r3, r4⟩ := hK.rel
  have cxy : Commute x y := hK.comm
  have cxw : Commute x w₀ := hxw.symm
  have cyw : Commute y w₀ := hyw.symm
  have hxyw : x * y * w₀ = w₀ * (x * y) := (cxw.mul_left cyw).eq
  rcases klein_flag_cases hK (leechQ w₀) with ⟨hx, hy, hxy⟩ | ⟨hx, hy, hxy⟩ | ⟨hx, hy, hxy⟩ |
    ⟨hx, hy, hxy⟩ | ⟨hx, hy, hxy⟩
  · simp [hx, hy, hxy] at hc
  ·
    exact ⟨w₀, hw₀, hwc, hxw.symm, hyw.symm, hx, hy⟩
  ·
    have hw : IsConj z₀ (w₀ * (x * y)) := (isConj_mul_iff I hG hw₀ hxyA hxyw).2 hxy
    have cx : Commute x (w₀ * (x * y)) := cxw.mul_right ((Commute.refl x).mul_right cxy)
    have cy : Commute y (w₀ * (x * y)) := cyw.mul_right (cxy.symm.mul_right (Commute.refl y))
    have e1 : w₀ * (x * y) * x = w₀ * y := by rw [mul_assoc, r3]
    have e2 : w₀ * (x * y) * y = w₀ * x := by rw [mul_assoc, r4]
    refine ⟨w₀ * (x * y), hw, mul_mem_cosetSet hK hwc (Or.inr (Or.inr (Or.inr rfl))), cx.eq,
      cy.eq, ?_, ?_⟩
    · refine mem_leechQ_of_isConj_mul I.sls I.tableV I.leech hG hxA hw cx.eq ?_
      rw [cx.eq, e1]
      exact isConj_a_mul_of_mem I hG hw₀ hyA hyw.symm hy
    · refine (isConj_mul_iff I hG hw hyA cy.eq).1 ?_
      rw [e2]
      exact (isConj_mul_iff I hG hw₀ hxA hxw.symm).2 hx
  ·
    have hw : IsConj z₀ (w₀ * y) := (isConj_mul_iff I hG hw₀ hyA hyw.symm).2 hy
    have cx : Commute x (w₀ * y) := cxw.mul_right cxy
    have cy : Commute y (w₀ * y) := cyw.mul_right (Commute.refl y)
    have e1 : w₀ * y * x = w₀ * (x * y) := by
      rw [mul_assoc, ← cxy.eq, ← mul_assoc]
    have e2 : w₀ * y * y = w₀ := by rw [mul_assoc, hK.sq_y, mul_one]
    refine ⟨w₀ * y, hw, mul_mem_cosetSet hK hwc (Or.inr (Or.inr (Or.inl rfl))), cx.eq, cy.eq,
      ?_, ?_⟩
    · refine mem_leechQ_of_isConj_mul I.sls I.tableV I.leech hG hxA hw cx.eq ?_
      rw [cx.eq, e1]
      exact isConj_a_mul_of_mem I hG hw₀ hxyA hxyw hxy
    · refine (isConj_mul_iff I hG hw hyA cy.eq).1 ?_
      rw [e2]
      exact hw₀
  · simp [hx, hy, hxy] at hc

end S365

end CFSG.Monster.GMS
