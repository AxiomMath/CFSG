module

public import CFSG.GH74.ThompsonOrderFormula
public import Mathlib.Combinatorics.Enumerative.DoubleCounting

import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.RuType.A65

open CFSG.ShultStronglyClosedTI.InvolutionCounting

variable {G : Type*} [Group G]

theorem mul_pow_eq {a b : G} (ha : a * a = 1) (hb : b * b = 1) (k : ℕ) :
    a * (a * b) ^ k = ((a * b) ^ k)⁻¹ * a := by
  have hk : a * (a * b) ^ k * a⁻¹ = ((a * b) ^ k)⁻¹ := by
    rw [← conj_pow, conj_mul_left_eq_inv ha hb, inv_pow]
  calc a * (a * b) ^ k = (a * (a * b) ^ k * a⁻¹) * a := by group
    _ = ((a * b) ^ k)⁻¹ * a := by rw [hk]

theorem isConj_mul_pow_half {a b : G} (ha : a * a = 1) (hb : b * b = 1) (m : ℕ) :
    (Even m → IsConj a (a * (a * b) ^ m)) ∧ (Odd m → IsConj a (b * (a * b) ^ m)) := by
  constructor
  · rintro ⟨i, rfl⟩
    refine isConj_iff.mpr ⟨((a * b) ^ i)⁻¹, ?_⟩
    rw [inv_inv]
    have h1 := mul_pow_eq ha hb i
    have h2 := mul_pow_eq ha hb (i + i)
    calc ((a * b) ^ i)⁻¹ * a * (a * b) ^ i = ((a * b) ^ i)⁻¹ * (a * (a * b) ^ i) := by group
      _ = ((a * b) ^ i)⁻¹ * (((a * b) ^ i)⁻¹ * a) := by rw [h1]
      _ = ((a * b) ^ (i + i))⁻¹ * a := by rw [pow_add]; group
      _ = a * (a * b) ^ (i + i) := h2.symm
  · rintro ⟨i, rfl⟩
    refine isConj_iff.mpr ⟨((a * b) ^ (i + 1))⁻¹, ?_⟩
    rw [inv_inv]
    have h1 := mul_pow_eq ha hb (i + 1)
    have h2 := mul_pow_eq ha hb (2 * i + 1 + 1)
    calc ((a * b) ^ (i + 1))⁻¹ * a * (a * b) ^ (i + 1)
        = ((a * b) ^ (i + 1))⁻¹ * (((a * b) ^ (i + 1))⁻¹ * a) := by rw [mul_assoc, h1]
      _ = ((a * b) ^ (2 * i + 1 + 1))⁻¹ * a := by
          rw [show 2 * i + 1 + 1 = (i + 1) + (i + 1) by ring, pow_add]; group
      _ = a * (a * b) ^ (2 * i + 1 + 1) := h2.symm
      _ = b * (a * b) ^ (2 * i + 1) := by
          rw [pow_succ', ← mul_assoc, ← mul_assoc, ha, one_mul]

variable [Finite G]

theorem pair_t_facts {z t : G} (hz : orderOf z = 2) (ht : orderOf t = 2) (hzt : ¬ IsConj z t)
    (hstar : ∀ u v : G, IsConj z u → IsConj z v → u * v = v * u → u * v ≠ 1 → IsConj z (u * v))
    {a b : G} (hp : (a, b) ∈ thompsonPairs z t t) :
    a * t = t * a ∧ IsConj z (b * t) ∧ b * t * t = t * (b * t) := by
  obtain ⟨hza, htb, hmem⟩ := hp
  have hz2 : z * z = 1 := mul_self_eq_one_of_orderOf_eq_two hz
  have ht2 : t * t = 1 := mul_self_eq_one_of_orderOf_eq_two ht
  have ha2 : a * a = 1 := mul_self_eq_one_of_isConj hz2 hza
  have hb2 : b * b = 1 := mul_self_eq_one_of_isConj ht2 htb
  have hab : ¬ IsConj a b := fun h => hzt (hza.trans (h.trans (isConj_comm.mp htb)))
  obtain ⟨hac0, hbc0⟩ := mem_centralizer_of_mem_thompsonPairs hz2 ht2 ht2 ⟨hza, htb, hmem⟩
  rw [Subgroup.mem_centralizer_singleton_iff] at hac0 hbc0
  have hac : a * t = t * a := hac0
  have hbc : b * t = t * b := hbc0
  obtain ⟨m, hm0, hm⟩ := exists_orderOf_mul_eq_two_mul ha2 hb2 hab
  have htm : t = (a * b) ^ m := (mem_zpowers_iff_eq_pow_half hm hm0 ht).mp hmem
  obtain ⟨hev, hodd⟩ := isConj_mul_pow_half ha2 hb2 m
  rcases Nat.even_or_odd m with he | ho
  · exfalso
    have h1 : IsConj z (a * t) := by
      rw [htm]
      exact hza.trans (hev he)
    have ht1 : t ≠ 1 := by
      intro h
      rw [h, orderOf_one] at ht
      exact absurd ht (by norm_num)
    have e1 : a * (a * t) = t := by rw [← mul_assoc, ha2, one_mul]
    have h2 := hstar a (a * t) hza h1 (by
      rw [e1]
      calc t = t * a * a := by rw [mul_assoc, ha2, mul_one]
        _ = a * t * a := by rw [hac]) (by rw [e1]; exact ht1)
    rw [e1] at h2
    exact hzt h2
  · refine ⟨hac, ?_, ?_⟩
    · rw [htm]
      exact hza.trans (hodd ho)
    · rw [mul_assoc, ht2, mul_one, ← mul_assoc, ← hbc, mul_assoc, ht2, mul_one]

theorem pairCount_t_le {z t : G} (hz : orderOf z = 2) (ht : orderOf t = 2) (hzt : ¬ IsConj z t)
    (hstar : ∀ u v : G, IsConj z u → IsConj z v → u * v = v * u → u * v ≠ 1 → IsConj z (u * v)) :
    thompsonPairCount z t t ≤ Nat.card {u : G // IsConj z u ∧ u * t = t * u} ^ 2 := by
  rw [sq, ← Nat.card_prod]
  let f : thompsonPairs z t t →
      {u : G // IsConj z u ∧ u * t = t * u} × {u : G // IsConj z u ∧ u * t = t * u} :=
    fun p => (⟨p.1.1, p.2.1, (pair_t_facts hz ht hzt hstar p.2).1⟩,
      ⟨p.1.2 * t, (pair_t_facts hz ht hzt hstar p.2).2.1,
        (pair_t_facts hz ht hzt hstar p.2).2.2⟩)
  refine Nat.card_le_card_of_injective f fun p q h => ?_
  have h1 : p.1.1 = q.1.1 := congrArg (fun x => (x.1 : G)) h
  have h2 : p.1.2 * t = q.1.2 * t := congrArg (fun x => (x.2 : G)) h
  exact Subtype.ext (Prod.ext h1 (mul_right_cancel h2))

theorem pairCount_z_le {z t : G} (hz : orderOf z = 2) (ht : orderOf t = 2) :
    thompsonPairCount z t z ≤ Nat.card {u : G // IsConj z u ∧ u * z = z * u} *
      Nat.card {v : G // IsConj t v ∧ v * z = z * v} := by
  rw [← Nat.card_prod]
  have hz2 : z * z = 1 := mul_self_eq_one_of_orderOf_eq_two hz
  have ht2 : t * t = 1 := mul_self_eq_one_of_orderOf_eq_two ht
  have hc : ∀ p : thompsonPairs z t z, p.1.1 * z = z * p.1.1 ∧ p.1.2 * z = z * p.1.2 := by
    intro p
    have h := mem_centralizer_of_mem_thompsonPairs hz2 ht2 hz2 p.2
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff] at h
    exact h
  let f : thompsonPairs z t z →
      {u : G // IsConj z u ∧ u * z = z * u} × {v : G // IsConj t v ∧ v * z = z * v} :=
    fun p => (⟨p.1.1, p.2.1, (hc p).1⟩, ⟨p.1.2, p.2.2.1, (hc p).2⟩)
  refine Nat.card_le_card_of_injective f fun p q h => ?_
  have h1 : p.1.1 = q.1.1 := congrArg (fun x => (x.1 : G)) h
  have h2 : p.1.2 = q.1.2 := congrArg (fun x => (x.2 : G)) h
  exact Subtype.ext (Prod.ext h1 h2)

theorem card_conj_mul_card_comm (x y : G) :
    Nat.card {u : G // IsConj x u} * Nat.card {v : G // IsConj y v ∧ v * x = x * v} =
      Nat.card {v : G // IsConj y v} * Nat.card {u : G // IsConj x u ∧ u * y = y * u} := by
  classical
  have := Fintype.ofFinite G
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  set X := Finset.univ.filter fun u : G => IsConj x u
  set Y := Finset.univ.filter fun v : G => IsConj y v
  have hdc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (fun u v : G => u * v = v * u) (s := X) (t := Y)
  have h1 : ∀ u ∈ X, (Y.bipartiteAbove (fun u v : G => u * v = v * u) u).card =
      (Finset.univ.filter fun v : G => IsConj y v ∧ v * x = x * v).card := by
    intro u hu
    obtain ⟨g, rfl⟩ := isConj_iff.mp (Finset.mem_filter.mp hu).2
    refine Finset.card_equiv
      { toFun := fun v => g⁻¹ * v * g
        invFun := fun v => g * v * g⁻¹
        left_inv := fun v => by simp only; group
        right_inv := fun v => by simp only; group } fun v => ?_
    simp only [Finset.mem_bipartiteAbove, Finset.mem_filter, Finset.mem_univ, true_and,
      Equiv.coe_fn_mk, Y]
    constructor
    · rintro ⟨hyv, hc⟩
      refine ⟨hyv.trans (isConj_iff.mpr ⟨g⁻¹, by group⟩), ?_⟩
      calc g⁻¹ * v * g * x = g⁻¹ * (v * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * v) * g := by rw [hc]
        _ = x * (g⁻¹ * v * g) := by group
    · rintro ⟨hyv, hc⟩
      refine ⟨hyv.trans (isConj_iff.mpr ⟨g, by group⟩), ?_⟩
      calc g * x * g⁻¹ * v = g * (x * (g⁻¹ * v * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * v * g) * x) * g⁻¹ := by rw [hc]
        _ = v * (g * x * g⁻¹) := by group
  have h2 : ∀ v ∈ Y, (X.bipartiteBelow (fun u v : G => u * v = v * u) v).card =
      (Finset.univ.filter fun u : G => IsConj x u ∧ u * y = y * u).card := by
    intro v hv
    obtain ⟨g, rfl⟩ := isConj_iff.mp (Finset.mem_filter.mp hv).2
    refine Finset.card_equiv
      { toFun := fun u => g⁻¹ * u * g
        invFun := fun u => g * u * g⁻¹
        left_inv := fun u => by simp only; group
        right_inv := fun u => by simp only; group } fun u => ?_
    simp only [Finset.mem_bipartiteBelow, Finset.mem_filter, Finset.mem_univ, true_and,
      Equiv.coe_fn_mk, X]
    constructor
    · rintro ⟨hxu, hc⟩
      refine ⟨hxu.trans (isConj_iff.mpr ⟨g⁻¹, by group⟩), ?_⟩
      calc g⁻¹ * u * g * y = g⁻¹ * (u * (g * y * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * y * g⁻¹) * u) * g := by rw [hc]
        _ = y * (g⁻¹ * u * g) := by group
    · rintro ⟨hxu, hc⟩
      refine ⟨hxu.trans (isConj_iff.mpr ⟨g, by group⟩), ?_⟩
      calc u * (g * y * g⁻¹) = g * ((g⁻¹ * u * g) * y) * g⁻¹ := by group
        _ = g * (y * (g⁻¹ * u * g)) * g⁻¹ := by rw [hc]
        _ = g * y * g⁻¹ * u := by group
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_const, Finset.sum_const,
    smul_eq_mul, smul_eq_mul] at hdc
  exact hdc

theorem card_centralizer_mul_eq (z t : G) :
    Nat.card (Subgroup.centralizer ({t} : Set G)) *
        Nat.card {v : G // IsConj t v ∧ v * z = z * v} =
      Nat.card (Subgroup.centralizer ({z} : Set G)) *
        Nat.card {u : G // IsConj z u ∧ u * t = t * u} := by
  have hz := card_centralizer_mul_card_conjugatesOf z
  have ht := card_centralizer_mul_card_conjugatesOf t
  have hdc := card_conj_mul_card_comm z t
  have hzc : Nat.card (conjugatesOf z) = Nat.card {u : G // IsConj z u} := rfl
  have htc : Nat.card (conjugatesOf t) = Nat.card {v : G // IsConj t v} := rfl
  rw [hzc] at hz
  rw [htc] at ht
  have hpos : 0 < Nat.card {u : G // IsConj z u} :=
    Nat.card_pos_iff.mpr ⟨⟨⟨z, IsConj.refl z⟩⟩, inferInstance⟩
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  calc Nat.card (Subgroup.centralizer ({t} : Set G)) *
        Nat.card {v : G // IsConj t v ∧ v * z = z * v} * Nat.card {u : G // IsConj z u} =
      Nat.card (Subgroup.centralizer ({t} : Set G)) * (Nat.card {u : G // IsConj z u} *
        Nat.card {v : G // IsConj t v ∧ v * z = z * v}) := by ring
    _ = Nat.card (Subgroup.centralizer ({t} : Set G)) * Nat.card {v : G // IsConj t v} *
        Nat.card {u : G // IsConj z u ∧ u * t = t * u} := by rw [hdc]; ring
    _ = Nat.card (Subgroup.centralizer ({z} : Set G)) * Nat.card {u : G // IsConj z u} *
        Nat.card {u : G // IsConj z u ∧ u * t = t * u} := by rw [ht, hz]
    _ = Nat.card (Subgroup.centralizer ({z} : Set G)) *
        Nat.card {u : G // IsConj z u ∧ u * t = t * u} * Nat.card {u : G // IsConj z u} := by
      ring

theorem index_centralizer_le {z t : G} (hz : orderOf z = 2) (ht : orderOf t = 2)
    (hzt : ¬ IsConj z t) (hcl : ∀ x : G, orderOf x = 2 → IsConj z x ∨ IsConj t x)
    (hstar : ∀ u v : G, IsConj z u → IsConj z v → u * v = v * u → u * v ≠ 1 → IsConj z (u * v)) :
    (Subgroup.centralizer ({z} : Set G)).index ≤
      Nat.card {u : G // IsConj z u ∧ u * t = t * u} *
        (Nat.card {u : G // IsConj z u ∧ u * t = t * u} +
          Nat.card {u : G // IsConj z u ∧ u * z = z * u}) := by
  obtain ⟨hform, -⟩ := CFSG.GH74.thompson_two_involution_class_order_formula hz ht hzt hcl
  have hat := pairCount_t_le hz ht hzt hstar
  have haz := pairCount_z_le hz ht
  have hdc := card_centralizer_mul_eq z t
  set c := Nat.card {u : G // IsConj z u ∧ u * t = t * u}
  set d := Nat.card {u : G // IsConj z u ∧ u * z = z * u}
  set e := Nat.card {v : G // IsConj t v ∧ v * z = z * v}
  set Cz := Nat.card (Subgroup.centralizer ({z} : Set G))
  set Ct := Nat.card (Subgroup.centralizer ({t} : Set G))
  have hG : Nat.card G ≤ Cz * (c * (c + d)) := by
    calc Nat.card G = Ct * thompsonPairCount z t z + Cz * thompsonPairCount z t t := hform
      _ ≤ Ct * (d * e) + Cz * c ^ 2 := by gcongr
      _ = d * (Ct * e) + Cz * c ^ 2 := by ring
      _ = Cz * (c * (c + d)) := by rw [hdc]; ring
  have hCpos : 0 < Cz := Nat.card_pos
  rw [← (Subgroup.centralizer ({z} : Set G)).card_mul_index] at hG
  exact Nat.le_of_mul_le_mul_left hG hCpos

end CFSG.Quasithin.RuType.A65
