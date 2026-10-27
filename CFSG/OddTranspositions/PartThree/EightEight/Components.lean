module

public import CFSG.OddTranspositions.PartThree.EightEight.CommProd
public import CFSG.OddTranspositions.PartThree.Statements
public import CFSG.Timmesfeld.Bridge.Asc72Basic
public import CFSG.Timmesfeld.Bridge.Asc72Triangle
public import CFSG.Timmesfeld.Closure.MinCex

import CFSG.OddTranspositions.PartThree.EightEight.Conjugator
import CFSG.OddTranspositions.PartThree.EightEight.Fibres
import CFSG.OddTranspositions.PartThree.EightEight.SecondKind

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity

variable {X : Type} [Group X] [Finite X] {E : Set X}

omit [Finite X] in
@[expose] def commProdAway (E : Set X) (x : X) : Subgroup X :=
  Subgroup.closure {g | ∃ y ∈ E, ∃ y' ∈ E, Commute y y' ∧
    QuotientGroup.mk' (derivedSeries X 2) y ≠ QuotientGroup.mk' (derivedSeries X 2) x ∧
    y * y' = g}

omit [Finite X] in
theorem commProdAway_le_commProd (E : Set X) (x : X) : commProdAway E x ≤ commProd E := by
  rw [commProdAway, Subgroup.closure_le]
  rintro g ⟨y, hy, y', hy', hyy', -, rfl⟩
  exact mul_mem_commProd hy hy' hyy'

omit [Finite X] in
theorem commProd_le_derivedSeries_two (hS : Setup X E) : commProd E ≤ derivedSeries X 2 := by
  rw [commProd, Subgroup.closure_le]
  rintro g ⟨y, hy, y', hy', hyy', rfl⟩
  exact mul_mem_derivedSeries_two_of_commute hS hy hy' hyy'

omit [Finite X] in
theorem exists_mem_mk_ne_of_derivedSeries_ne (hS : Setup X E)
    (hne : derivedSeries X 1 ≠ derivedSeries X 2) {y : X} :
    ∃ c ∈ E, QuotientGroup.mk' (derivedSeries X 2) c ≠
      QuotientGroup.mk' (derivedSeries X 2) y := by
  obtain ⟨a, ha, b, hb, hab⟩ := exists_mk_ne_of_derivedSeries_ne hS hne
  by_cases hya : QuotientGroup.mk' (derivedSeries X 2) y =
      QuotientGroup.mk' (derivedSeries X 2) a
  · exact ⟨b, hb, fun h => hab (hya.symm.trans h.symm)⟩
  · exact ⟨a, ha, fun h => hya h.symm⟩

omit [Finite X] in
theorem conj_mem_commProdAway (hS : Setup X E) {x g : X}
    (hg : QuotientGroup.mk' (derivedSeries X 2) g =
      QuotientGroup.mk' (derivedSeries X 2) x) {s : X}
    (hs : s ∈ commProdAway E x) : g * s * g⁻¹ ∈ commProdAway E x := by
  rw [commProdAway] at hs ⊢
  induction hs using Subgroup.closure_induction with
  | mem z hz =>
      rcases hz with ⟨y, hy, y', hy', hyy', hyx, rfl⟩
      refine Subgroup.subset_closure ⟨g * y * g⁻¹, hS.conj_mem g hy,
        g * y' * g⁻¹, hS.conj_mem g hy', hyy'.conj g, ?_, by group⟩
      intro h
      apply hyx
      have hφ : QuotientGroup.mk' (derivedSeries X 2) (g * y * g⁻¹) =
          QuotientGroup.mk' (derivedSeries X 2) g *
            QuotientGroup.mk' (derivedSeries X 2) y *
              (QuotientGroup.mk' (derivedSeries X 2) g)⁻¹ := by
        rw [map_mul, map_mul, map_inv]
      rw [hφ, hg] at h
      have hyφ : QuotientGroup.mk' (derivedSeries X 2) y =
          (QuotientGroup.mk' (derivedSeries X 2) x)⁻¹ *
            (QuotientGroup.mk' (derivedSeries X 2) x *
              QuotientGroup.mk' (derivedSeries X 2) y *
                (QuotientGroup.mk' (derivedSeries X 2) x)⁻¹) *
              QuotientGroup.mk' (derivedSeries X 2) x := by group
      rw [h] at hyφ
      rw [hyφ]
      group
  | one => simp
  | mul a b _ _ iha ihb =>
      have hconj : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      rw [hconj]
      exact Subgroup.mul_mem _ iha ihb
  | inv a _ iha =>
      have hconj : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
      rw [hconj]
      exact Subgroup.inv_mem _ iha

theorem commProdAway_eq_commProd (h86 : Lemma8_6) (hS : Setup X E)
    (hne : derivedSeries X 1 ≠ derivedSeries X 2) (x : X) :
    commProdAway E x = commProd E := by
  refine le_antisymm (commProdAway_le_commProd E x) ?_
  rw [commProd, Subgroup.closure_le]
  rintro g ⟨y, hy, y', hy', hyy', rfl⟩
  by_cases hyx : QuotientGroup.mk' (derivedSeries X 2) y =
      QuotientGroup.mk' (derivedSeries X 2) x
  · by_cases hne' : y = y'
    · subst y'
      rw [hS.oddT.mul_self_eq_one hy]
      exact Subgroup.one_mem _
    · obtain ⟨c, hc, hcy⟩ := exists_mem_mk_ne_of_derivedSeries_ne hS hne
      obtain ⟨c', hc', hcc', -, hconj⟩ :=
        exists_conj_eq_of_mk_ne h86 hS hy hy' hc hyy' hne' hcy
      have hcx : QuotientGroup.mk' (derivedSeries X 2) c ≠
          QuotientGroup.mk' (derivedSeries X 2) x := by
        rwa [hyx] at hcy
      have hcc' : Commute c' c := hcc'.symm
      have hc'c : QuotientGroup.mk' (derivedSeries X 2) c' =
          QuotientGroup.mk' (derivedSeries X 2) c := mk_eq_mk_of_commute hS hc' hc hcc'
      have hsA : c' * c ∈ commProdAway E x := by
        refine Subgroup.subset_closure ⟨c', hc', c, hc, hcc', ?_, rfl⟩
        rw [hc'c]
        exact hcx
      have hy'y : QuotientGroup.mk' (derivedSeries X 2) y' =
          QuotientGroup.mk' (derivedSeries X 2) y :=
        mk_eq_mk_of_commute hS hy' hy hyy'.symm
      have hy'x : QuotientGroup.mk' (derivedSeries X 2) y' =
          QuotientGroup.mk' (derivedSeries X 2) x := hy'y.trans hyx
      have hconjA : y' * (c' * c)⁻¹ * y'⁻¹ ∈ commProdAway E x :=
        conj_mem_commProdAway hS hy'x (Subgroup.inv_mem _ hsA)
      have hprod : y * y' = (c' * c) * (y' * (c' * c)⁻¹ * y'⁻¹) := by
        rw [← hconj, hS.oddT.inv_eq hy']
        group
      rw [hprod]
      exact Subgroup.mul_mem _ hsA hconjA
  · exact Subgroup.subset_closure ⟨y, hy, y', hy', hyy', hyx, rfl⟩

theorem reach_conj_of_mem_commProd (h86 : Lemma8_6) (hS : Setup X E)
    (hne : derivedSeries X 1 ≠ derivedSeries X 2) {g c : X} (hg : g ∈ commProd E)
    (hc : c ∈ E) : Reach E c (g * c * g⁻¹) := by
  let φ : X →* X ⧸ derivedSeries X 2 := QuotientGroup.mk' (derivedSeries X 2)
  have hgc : g ∈ commProdAway E c := by
    rw [commProdAway_eq_commProd h86 hS hne c]
    exact hg
  have key : ∀ g ∈ commProdAway E c, ∀ d ∈ E, φ d = φ c → Reach E d (g * d * g⁻¹) := by
    intro g hg
    rw [commProdAway] at hg
    induction hg using Subgroup.closure_induction with
    | mem z hz =>
        rintro d hd hdφ
        rcases hz with ⟨y, hy, y', hy', hyy', hyc, rfl⟩
        by_cases hne' : y = y'
        · subst y'
          rw [hS.oddT.mul_self_eq_one hy]
          simpa using reach_refl (D := E) d
        · have hdy : φ d ≠ φ y := fun h => hyc (h.symm.trans hdφ)
          have ht : (y * y') * d * (y * y')⁻¹ ∈ E := hS.conj_mem (y * y') hd
          have hcomm := commute_conj_of_mk_ne hS hy hy' hd hyy' hdy
          exact reach_of_commute hd ht hcomm.symm
    | one =>
        rintro d hd hdφ
        simpa using reach_refl (D := E) d
    | mul a b ha hb iha ihb =>
        rintro d hd hdφ
        have hbder : b ∈ derivedSeries X 2 :=
          commProd_le_derivedSeries_two hS (commProdAway_le_commProd E c hb)
        have hb1 : φ b = 1 := by
          rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
          exact hbder
        have hbd : φ (b * d * b⁻¹) = φ c := by
          rw [map_mul, map_mul, map_inv, hb1, hdφ]
          group
        have h1 := ihb d hd hdφ
        have h2 := iha (b * d * b⁻¹) (hS.conj_mem b hd) hbd
        have heq : (a * b) * d * (a * b)⁻¹ = a * (b * d * b⁻¹) * a⁻¹ := by group
        rw [heq]
        exact reach_trans h1 h2
    | inv a _ iha =>
        rintro d hd hdφ
        have h1 := reach_conj hS.normal a⁻¹ (iha d hd hdφ)
        have h2 : a⁻¹ * (a * d * a⁻¹) * (a⁻¹)⁻¹ = d := by group
        rw [h2] at h1
        exact reach_symm h1
  exact key g hgc c hc rfl

omit [Finite X] in
theorem mul_mem_commProd_of_reach (hS : Setup X E) {x y : X} (hx : x ∈ E)
    (h : Reach E x y) : x * y ∈ commProd E := by
  let S : Set X := {y | y ∈ E ∧ x * y ∈ commProd E}
  have hxS : x ∈ S := by
    refine ⟨hx, ?_⟩
    rw [hS.oddT.mul_self_eq_one hx]
    exact Subgroup.one_mem _
  have hclosed : ∀ z ∈ S, ∀ y ∈ E, Commute z y → y ∈ S := by
    rintro z ⟨hzE, hxz⟩ y hy hzy
    refine ⟨hy, ?_⟩
    have hzyN : z * y ∈ commProd E := mul_mem_commProd hzE hy hzy
    have hz2 : z * z = 1 := hS.oddT.mul_self_eq_one hzE
    have hxy : x * y = (x * z) * (z * y) := by
      rw [mul_assoc, ← mul_assoc z, hz2, one_mul]
    rw [hxy]
    exact Subgroup.mul_mem _ hxz hzyN
  exact (mem_of_reach hclosed hxS h).2

omit [Finite X] in
theorem exists_conj_mem_commProd_of_odd (hS : Setup X E) {x y : X} (hx : x ∈ E) (hy : y ∈ E)
    (hxy : x * y ∈ commProd E) (hodd : Odd (orderOf (x * y))) :
    ∃ g ∈ commProd E, g * x * g⁻¹ = y := by
  obtain ⟨k, hk⟩ := hodd
  refine ⟨(x * y) ^ k, Subgroup.pow_mem _ hxy k, ?_⟩
  have hx2 : x * x = 1 := hS.oddT.mul_self_eq_one hx
  have hy2 : y * y = 1 := hS.oddT.mul_self_eq_one hy
  have hpow : (x * y) ^ (2 * k + 1) = 1 := hk ▸ pow_orderOf_eq_one _
  have hc := CFSG.Timmesfeld.mul_zpow_mul_eq_zpow_neg_mul hx2 hy2 (-(k : ℤ))
  rw [neg_neg, zpow_natCast, zpow_neg, zpow_natCast] at hc
  calc (x * y) ^ k * x * ((x * y) ^ k)⁻¹ = (x * y) ^ k * (x * y) ^ k * x := by
        rw [mul_assoc, hc, mul_assoc]
    _ = (x * y) ^ (2 * k + 1) * (x * y)⁻¹ * x := by
        rw [← pow_add, pow_succ, mul_inv_cancel_right, two_mul]
    _ = y := by
        rw [hpow, one_mul, mul_inv_rev, inv_mul_cancel_right,
          inv_eq_of_mul_eq_one_right hy2]

theorem reach_iff_mul_mem_commProd (h86 : Lemma8_6) (hS : Setup X E)
    (hne : derivedSeries X 1 ≠ derivedSeries X 2) {x y : X} (hx : x ∈ E) (hy : y ∈ E) :
    Reach E x y ↔ x * y ∈ commProd E := by
  constructor
  · exact mul_mem_commProd_of_reach hS hx
  · intro hxy
    by_cases hcomm : Commute x y
    · exact reach_of_commute hx hy hcomm
    · have hodd : Odd (orderOf (x * y)) := hS.oddT.odd_of_not_commute hx hy hcomm
      obtain ⟨g, hgN, hgconj⟩ := exists_conj_mem_commProd_of_odd hS hx hy hxy hodd
      rw [← hgconj]
      exact reach_conj_of_mem_commProd h86 hS hne hgN hx

theorem orderOf_mul_eq_four_of_not_reach (h86 : Lemma8_6) (hS : Setup X E)
    (hne : derivedSeries X 1 ≠ derivedSeries X 2) {x w y : X} (ht : IsTriangle E x w y)
    (hw : ¬ Reach E x w) : orderOf (x * y * w) = 4 := by
  have hN : (commProd E).Normal := commProd_normal hS.normal
  let φ₀ : X →* X ⧸ commProd E := QuotientGroup.mk' (commProd E)
  have hx : x ∈ E := ht.1
  have hy : y ∈ E := ht.2.1
  have hwE : w ∈ E := ht.2.2.1
  have hxy : Commute x y := ht.2.2.2.2.1
  have huv : φ₀ x = φ₀ y :=
    mk_eq_mk_of_commute_of_commProd_le hS.oddT le_rfl hx hy (hxy.map φ₀)
  have hxwN : x * w ∉ commProd E := fun hm =>
    hw ((reach_iff_mul_mem_commProd h86 hS hne hx hwE).mpr hm)
  have hxwφ : φ₀ (x * w) ≠ 1 := by
    intro h
    apply hxwN
    rw [QuotientGroup.mk'_apply] at h
    exact (QuotientGroup.eq_one_iff (N := commProd E) (x * w)).mp h
  have hodd : Odd (orderOf (φ₀ x * φ₀ w)) := by
    have h := hS.oddT.odd_of_not_commute hx hwE ht.2.2.2.2.2.1
    rw [show φ₀ x * φ₀ w = φ₀ (x * w) by rw [map_mul]]
    exact Odd.of_dvd_nat h (orderOf_map_dvd φ₀ (x * w))
  have h1 : 1 < orderOf (φ₀ x * φ₀ w) := by
    have hpos : 0 < orderOf (φ₀ x * φ₀ w) := orderOf_pos _
    have hne1 : orderOf (φ₀ x * φ₀ w) ≠ 1 := by
      intro ho
      have hprod : φ₀ x * φ₀ w = φ₀ (x * w) := by rw [map_mul]
      rw [hprod] at ho
      exact hxwφ (orderOf_eq_one_iff.mp ho)
    omega
  exact CFSG.OddTranspositions.PartThree.orderOf_mul_eq_four_of_map_eq
    hS.oddT hS.normal ht φ₀ huv hodd h1

end CFSG.OddTranspositions.PartThree.EightEight

end
