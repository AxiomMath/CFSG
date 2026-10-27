module

public import Mathlib.GroupTheory.OrderOfElement

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Group
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Positivity.Basic

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.InvolutionCounting

variable {G : Type*} [Group G]

section Dihedral

variable {v s c t x : G}

theorem conj_zpow_eq_inv (h : t * c * t⁻¹ = c⁻¹) (k : ℤ) :
    t * c ^ k * t⁻¹ = (c ^ k)⁻¹ := by
  rw [← conj_zpow, h, inv_zpow]

theorem conj_mul_left_eq_inv (hv : v * v = 1) (hs : s * s = 1) :
    v * (v * s) * v⁻¹ = (v * s)⁻¹ := by
  rw [inv_eq_of_mul_eq_one_right hv, mul_inv_rev, inv_eq_of_mul_eq_one_right hs,
    inv_eq_of_mul_eq_one_right hv, ← mul_assoc, hv, one_mul]

theorem conj_mul_right_eq_inv (hv : v * v = 1) (hs : s * s = 1) :
    s * (v * s) * s⁻¹ = (v * s)⁻¹ := by
  rw [inv_eq_of_mul_eq_one_right hs, mul_inv_rev, inv_eq_of_mul_eq_one_right hs,
    inv_eq_of_mul_eq_one_right hv, mul_assoc, mul_assoc, hs, mul_one]

theorem commute_of_mem_zpowers (h : t * c * t⁻¹ = c⁻¹) (hx : x ∈ Subgroup.zpowers c)
    (hx2 : x * x = 1) : Commute t x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hconj := conj_zpow_eq_inv h k
  rw [inv_eq_of_mul_eq_one_right hx2] at hconj
  exact mul_inv_eq_iff_eq_mul.mp hconj

theorem mul_self_eq_one_of_isConj {u : G} (hu : u * u = 1) (h : IsConj u v) : v * v = 1 := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  rw [show g * u * g⁻¹ * (g * u * g⁻¹) = g * (u * u) * g⁻¹ by group, hu, mul_one,
    mul_inv_cancel]

theorem isConj_of_odd_orderOf_mul (hv : v * v = 1) (hs : s * s = 1)
    (hodd : Odd (orderOf (v * s))) : IsConj v s := by
  obtain ⟨k, hk⟩ := hodd
  set c := v * s with hc
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hpow : ∀ j : ℕ, v * c ^ j = (c ^ j)⁻¹ * v := by
    intro j
    have h := congrArg (· ^ j) (conj_mul_left_eq_inv hv hs)
    simp only [conj_pow, inv_pow] at h
    calc v * c ^ j = (v * c ^ j * v⁻¹) * v := by group
      _ = (c ^ j)⁻¹ * v := by rw [h]
  have hcm : c ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one c
  refine isConj_iff.mpr ⟨(c ^ (k + 1))⁻¹, ?_⟩
  rw [inv_inv, mul_assoc, hpow (k + 1), ← mul_assoc, ← mul_inv_rev, ← pow_add]
  have h2 : c ^ (k + 1 + (k + 1)) = c := by
    rw [show k + 1 + (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, hcm, one_mul]
  rw [h2, hc, mul_inv_rev, hsinv, hvinv, mul_assoc, hv, mul_one]

theorem exists_orderOf_mul_eq_two_mul [Finite G] (hv : v * v = 1) (hs : s * s = 1)
    (hvs : ¬ IsConj v s) : ∃ d : ℕ, d ≠ 0 ∧ orderOf (v * s) = 2 * d := by
  have heven : Even (orderOf (v * s)) := by
    by_contra h
    exact hvs (isConj_of_odd_orderOf_mul hv hs (Nat.not_even_iff_odd.mp h))
  obtain ⟨d, hd⟩ := heven
  refine ⟨d, ?_, by omega⟩
  rintro rfl
  exact (orderOf_pos (v * s)).ne' (by omega)

theorem orderOf_pow_half {d : ℕ} (hd : orderOf c = 2 * d) (hd0 : d ≠ 0) :
    orderOf (c ^ d) = 2 := by
  rw [orderOf_pow_of_dvd hd0 (hd ▸ dvd_mul_left d 2), hd, Nat.mul_div_cancel _ (by omega)]

theorem mem_zpowers_iff_eq_pow_half {d : ℕ} (hd : orderOf c = 2 * d) (hd0 : d ≠ 0)
    (hx : orderOf x = 2) : x ∈ Subgroup.zpowers c ↔ x = c ^ d := by
  refine ⟨fun hmem => ?_, fun h => h ▸ Subgroup.npow_mem_zpowers c d⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hsq : c ^ (k * 2) = 1 := by
    rw [zpow_mul, zpow_two, ← pow_two, ← hx, pow_orderOf_eq_one]
  have hdvd : (d : ℤ) * 2 ∣ k * 2 := by
    have := orderOf_dvd_iff_zpow_eq_one.mpr hsq
    rw [hd] at this
    simpa [mul_comm] using this
  obtain ⟨m, rfl⟩ := (mul_dvd_mul_iff_right two_ne_zero).mp hdvd
  have hy : c ^ ((d : ℤ) * m) = (c ^ d) ^ (m % 2) := by
    rw [zpow_mul, zpow_natCast, ← zpow_mod_orderOf, orderOf_pow_half hd hd0, Nat.cast_ofNat]
  rw [hy] at hx ⊢
  rcases Int.emod_two_eq_zero_or_one m with hm | hm
  · rw [hm, zpow_zero, orderOf_one] at hx
    exact absurd hx (by norm_num)
  · rw [hm, zpow_one]

theorem orderOf_eq_of_isConj {a b : G} (h : IsConj a b) : orderOf a = orderOf b := by
  obtain ⟨c, hc⟩ := h
  exact SemiconjBy.orderOf_eq _ hc

theorem mem_zpowers_mul_iff [Finite G] (hv : v * v = 1) (hs : s * s = 1) (hvs : ¬ IsConj v s)
    (hx : orderOf x = 2) :
    x ∈ Subgroup.zpowers (v * s) ↔ x = (v * s) ^ (orderOf (v * s) / 2) := by
  obtain ⟨d, hd0, hd⟩ := exists_orderOf_mul_eq_two_mul hv hs hvs
  rw [mem_zpowers_iff_eq_pow_half hd hd0 hx, hd, Nat.mul_div_cancel_left d two_pos]

theorem orderOf_pow_orderOf_mul_div_two [Finite G] (hv : v * v = 1) (hs : s * s = 1)
    (hvs : ¬ IsConj v s) : orderOf ((v * s) ^ (orderOf (v * s) / 2)) = 2 := by
  obtain ⟨d, hd0, hd⟩ := exists_orderOf_mul_eq_two_mul hv hs hvs
  rw [hd, Nat.mul_div_cancel_left d two_pos]
  exact orderOf_pow_half hd hd0

end Dihedral

@[expose] def thompsonPairs (u z w : G) : Set (G × G) :=
  {p | IsConj u p.1 ∧ IsConj z p.2 ∧ w ∈ Subgroup.zpowers (p.1 * p.2)}

@[expose] def thompsonPairCount (u z w : G) : ℕ :=
  Nat.card (thompsonPairs u z w)

@[simp]
theorem mem_thompsonPairs {u z w : G} {p : G × G} :
    p ∈ thompsonPairs u z w ↔
      IsConj u p.1 ∧ IsConj z p.2 ∧ w ∈ Subgroup.zpowers (p.1 * p.2) :=
  Iff.rfl

theorem isConj_conj_iff {a b : G} (g : G) : IsConj a (g * b * g⁻¹) ↔ IsConj a b :=
  ⟨fun h => h.trans (isConj_iff.mpr ⟨g⁻¹, by group⟩),
    fun h => h.trans (isConj_iff.mpr ⟨g, rfl⟩)⟩

theorem conj_mem_thompsonPairs_iff {u z w : G} (g : G) {p : G × G} :
    (g * p.1 * g⁻¹, g * p.2 * g⁻¹) ∈ thompsonPairs u z (g * w * g⁻¹) ↔
      p ∈ thompsonPairs u z w := by
  have hmul : g * p.1 * g⁻¹ * (g * p.2 * g⁻¹) = g * (p.1 * p.2) * g⁻¹ := by group
  simp only [mem_thompsonPairs, isConj_conj_iff, hmul, Subgroup.mem_zpowers_iff, conj_zpow,
    mul_left_inj, mul_right_inj]

theorem thompsonPairCount_conj (u z w g : G) :
    thompsonPairCount u z (g * w * g⁻¹) = thompsonPairCount u z w := by
  let e : G × G ≃ G × G := (MulAut.conj g).toEquiv.prodCongr (MulAut.conj g).toEquiv
  exact (Nat.card_congr (e.subtypeEquiv fun p => (conj_mem_thompsonPairs_iff g).symm)).symm

theorem thompsonPairCount_eq_of_isConj (u z : G) {w w' : G} (h : IsConj w w') :
    thompsonPairCount u z w = thompsonPairCount u z w' := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  exact (thompsonPairCount_conj u z w g).symm

theorem mem_centralizer_of_mem_thompsonPairs {u z w : G} (hu : u * u = 1) (hz : z * z = 1)
    (hw : w * w = 1) {p : G × G} (hp : p ∈ thompsonPairs u z w) :
    p.1 ∈ Subgroup.centralizer {w} ∧ p.2 ∈ Subgroup.centralizer {w} := by
  obtain ⟨h1, h2, hmem⟩ := hp
  have hv := mul_self_eq_one_of_isConj hu h1
  have hs := mul_self_eq_one_of_isConj hz h2
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  exact ⟨(commute_of_mem_zpowers (conj_mul_left_eq_inv hv hs) hmem hw).eq,
    (commute_of_mem_zpowers (conj_mul_right_eq_inv hv hs) hmem hw).eq⟩

theorem card_centralizer_mul_card_conjugatesOf (g : G) :
    Nat.card (Subgroup.centralizer {g}) * Nat.card (conjugatesOf g) = Nat.card G := by
  rw [Nat.card_coe_set_eq, ← Subgroup.index_centralizer_eq_ncard, Subgroup.card_mul_index]

theorem card_conjugatesOf_mul_eq_sum [Fintype G] {u z : G} (hu : u * u = 1) (hz : z * z = 1)
    (huz : ¬ IsConj u z) :
    Nat.card (conjugatesOf u) * Nat.card (conjugatesOf z) =
      ∑ w ∈ Finset.univ.filter (fun w : G => orderOf w = 2), thompsonPairCount u z w := by
  classical
  set P : Finset (G × G) := (conjugatesOf u).toFinset ×ˢ (conjugatesOf z).toFinset
  have hPcard : P.card = Nat.card (conjugatesOf u) * Nat.card (conjugatesOf z) := by
    rw [Finset.card_product, Nat.card_eq_card_toFinset, Nat.card_eq_card_toFinset]
  have hmemP : ∀ p : G × G, p ∈ P ↔ IsConj u p.1 ∧ IsConj z p.2 := fun p => by
    rw [Finset.mem_product, Set.mem_toFinset, Set.mem_toFinset]
    rfl
  have hnc : ∀ p ∈ P, p.1 * p.1 = 1 ∧ p.2 * p.2 = 1 ∧ ¬ IsConj p.1 p.2 := by
    intro p hp
    rw [hmemP] at hp
    exact ⟨mul_self_eq_one_of_isConj hu hp.1, mul_self_eq_one_of_isConj hz hp.2,
      fun h => huz ((hp.1.trans h).trans (isConj_comm.mp hp.2))⟩
  set f : G × G → G := fun p => (p.1 * p.2) ^ (orderOf (p.1 * p.2) / 2)
  have hmaps : ∀ p ∈ P, f p ∈ Finset.univ.filter (fun w : G => orderOf w = 2) := by
    intro p hp
    obtain ⟨h1, h2, h3⟩ := hnc p hp
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, orderOf_pow_orderOf_mul_div_two h1 h2 h3⟩
  rw [← hPcard, Finset.card_eq_sum_card_fiberwise fun p hp => hmaps p hp]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [Finset.mem_filter] at hw
  rw [thompsonPairCount, Nat.card_eq_card_toFinset]
  congr 1
  ext p
  rw [Finset.mem_filter, Set.mem_toFinset, mem_thompsonPairs, hmemP, and_assoc]
  refine and_congr_right fun h1 => and_congr_right fun h2 => ?_
  obtain ⟨hv, hs, hvs⟩ := hnc p ((hmemP p).mpr ⟨h1, h2⟩)
  rw [mem_zpowers_mul_iff hv hs hvs hw.2, eq_comm]

theorem sum_involutions_eq_sum_transversal [Fintype G] (T : Finset G)
    (hT : ∀ w ∈ T, orderOf w = 2) (hTrep : ∀ x : G, orderOf x = 2 → ∃! w, w ∈ T ∧ IsConj w x)
    (a : G → ℕ) (ha : ∀ w w' : G, IsConj w w' → a w = a w') :
    ∑ w ∈ Finset.univ.filter (fun w : G => orderOf w = 2), a w =
      ∑ t ∈ T, Nat.card (conjugatesOf t) * a t := by
  classical
  have hunion : Finset.univ.filter (fun w : G => orderOf w = 2) =
      T.biUnion fun t => (conjugatesOf t).toFinset := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Set.mem_toFinset]
    constructor
    · intro hx
      obtain ⟨t, ⟨htT, htx⟩, -⟩ := hTrep x hx
      exact ⟨t, htT, htx⟩
    · rintro ⟨t, htT, htx⟩
      exact (orderOf_eq_of_isConj htx).symm.trans (hT t htT)
  have hdisj : (T : Set G).PairwiseDisjoint fun t => (conjugatesOf t).toFinset := by
    intro t ht t' ht' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx hx'
    rw [Set.mem_toFinset] at hx hx'
    have hxinv : orderOf x = 2 := (orderOf_eq_of_isConj hx).symm.trans (hT t ht)
    obtain ⟨w, -, huniq⟩ := hTrep x hxinv
    exact hne ((huniq t ⟨ht, hx⟩).trans (huniq t' ⟨ht', hx'⟩).symm)
  rw [hunion, Finset.sum_biUnion hdisj]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_const_nat fun x hx =>
      (ha t x (show x ∈ conjugatesOf t from Set.mem_toFinset.mp hx)).symm,
    Nat.card_eq_card_toFinset]

theorem mul_self_eq_one_of_orderOf_eq_two {u : G} (hu : orderOf u = 2) : u * u = 1 := by
  rw [← sq, ← hu, pow_orderOf_eq_one]

theorem card_eq_sum_transversal [Finite G] {u z : G} (hu : orderOf u = 2) (hz : orderOf z = 2)
    (huz : ¬ IsConj u z) (T : Finset G) (hT : ∀ w ∈ T, orderOf w = 2)
    (hTrep : ∀ x : G, orderOf x = 2 → ∃! w, w ∈ T ∧ IsConj w x) :
    (Nat.card G : ℚ) = ∑ w ∈ T, (thompsonPairCount u z w : ℚ) *
      Nat.card (Subgroup.centralizer {u}) * Nat.card (Subgroup.centralizer {z}) /
        Nat.card (Subgroup.centralizer {w}) := by
  have := Fintype.ofFinite G
  have hcount := card_conjugatesOf_mul_eq_sum (mul_self_eq_one_of_orderOf_eq_two hu)
    (mul_self_eq_one_of_orderOf_eq_two hz) huz
  rw [sum_involutions_eq_sum_transversal T hT hTrep _
    fun _ _ h => thompsonPairCount_eq_of_isConj u z h] at hcount
  have hN : (Nat.card G : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have horbit : ∀ g : G, (Nat.card (Subgroup.centralizer {g}) : ℚ) *
      Nat.card (conjugatesOf g) = Nat.card G := fun g => by
    exact_mod_cast card_centralizer_mul_card_conjugatesOf g
  have hterm : ∀ w ∈ T, (thompsonPairCount u z w : ℚ) *
      Nat.card (Subgroup.centralizer {u}) * Nat.card (Subgroup.centralizer {z}) /
        Nat.card (Subgroup.centralizer {w}) =
      Nat.card (Subgroup.centralizer {u}) * Nat.card (Subgroup.centralizer {z}) / Nat.card G *
        (Nat.card (conjugatesOf w) * thompsonPairCount u z w) := by
    intro w _
    have hcw : (Nat.card (Subgroup.centralizer {w}) : ℚ) ≠ 0 :=
      left_ne_zero_of_mul ((horbit w).symm ▸ hN)
    have hkw : (Nat.card (conjugatesOf w) : ℚ) ≠ 0 :=
      right_ne_zero_of_mul ((horbit w).symm ▸ hN)
    rw [← horbit w]
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hsum : (∑ w ∈ T, (Nat.card (conjugatesOf w) : ℚ) * thompsonPairCount u z w) =
      Nat.card (conjugatesOf u) * Nat.card (conjugatesOf z) := by
    exact_mod_cast hcount.symm
  rw [hsum, div_mul_eq_mul_div, eq_div_iff hN]
  calc (Nat.card G : ℚ) * Nat.card G =
        (Nat.card (Subgroup.centralizer {u}) * Nat.card (conjugatesOf u)) *
          (Nat.card (Subgroup.centralizer {z}) * Nat.card (conjugatesOf z)) := by
        rw [horbit u, horbit z]
    _ = _ := by ring

theorem card_eq_of_thompsonPairCount_support [Finite G] {u z : G} (hu : orderOf u = 2)
    (hz : orderOf z = 2) (huz : ¬ IsConj u z)
    (hsupp : ∀ w : G, orderOf w = 2 → ¬ IsConj u w → ¬ IsConj z w →
      thompsonPairCount u z w = 0) :
    Nat.card G = Nat.card (Subgroup.centralizer {z}) * thompsonPairCount u z u +
      Nat.card (Subgroup.centralizer {u}) * thompsonPairCount u z z := by
  classical
  have := Fintype.ofFinite G
  have hcount := card_conjugatesOf_mul_eq_sum (mul_self_eq_one_of_orderOf_eq_two hu)
    (mul_self_eq_one_of_orderOf_eq_two hz) huz
  have hsub : (conjugatesOf u).toFinset ∪ (conjugatesOf z).toFinset ⊆
      Finset.univ.filter (fun w : G => orderOf w = 2) := by
    intro x hx
    rw [Finset.mem_union, Set.mem_toFinset, Set.mem_toFinset] at hx
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hx with hx | hx
    · exact (orderOf_eq_of_isConj hx).symm.trans hu
    · exact (orderOf_eq_of_isConj hx).symm.trans hz
  have hvanish : ∀ x ∈ Finset.univ.filter (fun w : G => orderOf w = 2),
      x ∉ (conjugatesOf u).toFinset ∪ (conjugatesOf z).toFinset →
        thompsonPairCount u z x = 0 := by
    intro x hx hxn
    rw [Finset.mem_union, Set.mem_toFinset, Set.mem_toFinset, not_or] at hxn
    exact hsupp x (Finset.mem_filter.mp hx).2 hxn.1 hxn.2
  have hdisj : Disjoint (conjugatesOf u).toFinset (conjugatesOf z).toFinset := by
    rw [Finset.disjoint_left]
    intro x hxu hxz
    rw [Set.mem_toFinset] at hxu hxz
    exact huz (hxu.trans (isConj_comm.mp hxz))
  have hconst : ∀ y : G, ∀ x ∈ (conjugatesOf y).toFinset,
      thompsonPairCount u z x = thompsonPairCount u z y := fun y x hx =>
    (thompsonPairCount_eq_of_isConj u z (show x ∈ conjugatesOf y from
      Set.mem_toFinset.mp hx)).symm
  rw [← Finset.sum_subset hsub hvanish, Finset.sum_union hdisj,
    Finset.sum_const_nat (hconst u), Finset.sum_const_nat (hconst z),
    ← Nat.card_eq_card_toFinset, ← Nat.card_eq_card_toFinset] at hcount
  have hu' := card_centralizer_mul_card_conjugatesOf u
  have hz' := card_centralizer_mul_card_conjugatesOf z
  refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := G)) ?_
  calc Nat.card G * Nat.card G =
        (Nat.card (Subgroup.centralizer {u}) * Nat.card (conjugatesOf u)) *
          (Nat.card (Subgroup.centralizer {z}) * Nat.card (conjugatesOf z)) := by
        rw [hu', hz']
    _ = Nat.card (Subgroup.centralizer {u}) * Nat.card (Subgroup.centralizer {z}) *
          (Nat.card (conjugatesOf u) * Nat.card (conjugatesOf z)) := by ring
    _ = Nat.card (Subgroup.centralizer {z}) *
            (Nat.card (Subgroup.centralizer {u}) * Nat.card (conjugatesOf u)) *
            thompsonPairCount u z u +
          Nat.card (Subgroup.centralizer {u}) *
            (Nat.card (Subgroup.centralizer {z}) * Nat.card (conjugatesOf z)) *
            thompsonPairCount u z z := by rw [hcount]; ring
    _ = _ := by rw [hu', hz']; ring

theorem thompson_all_involution_classes_order_formula [Finite G] {u z : G}
    (hu : orderOf u = 2) (hz : orderOf z = 2) (huz : ¬ IsConj u z) (T : Finset G)
    (hT : ∀ w ∈ T, orderOf w = 2)
    (hTrep : ∀ x : G, orderOf x = 2 → ∃! w, w ∈ T ∧ IsConj w x) :
    (∀ w : G, orderOf w = 2 → ∀ p ∈ thompsonPairs u z w,
      p.1 ∈ Subgroup.centralizer {w} ∧ p.2 ∈ Subgroup.centralizer {w}) ∧
    (∀ w w' : G, IsConj w w' → thompsonPairCount u z w = thompsonPairCount u z w') ∧
    ((Nat.card G : ℚ) = ∑ w ∈ T, (thompsonPairCount u z w : ℚ) *
      Nat.card (Subgroup.centralizer {u}) * Nat.card (Subgroup.centralizer {z}) /
        Nat.card (Subgroup.centralizer {w})) ∧
    ((∀ w : G, orderOf w = 2 → ¬ IsConj u w → ¬ IsConj z w →
        thompsonPairCount u z w = 0) →
      Nat.card G = Nat.card (Subgroup.centralizer {z}) * thompsonPairCount u z u +
        Nat.card (Subgroup.centralizer {u}) * thompsonPairCount u z z) :=
  ⟨fun _ hw _ hp => mem_centralizer_of_mem_thompsonPairs (mul_self_eq_one_of_orderOf_eq_two hu)
      (mul_self_eq_one_of_orderOf_eq_two hz) (mul_self_eq_one_of_orderOf_eq_two hw) hp,
    fun _ _ h => thompsonPairCount_eq_of_isConj u z h,
    card_eq_sum_transversal hu hz huz T hT hTrep,
    card_eq_of_thompsonPairCount_support hu hz huz⟩

end CFSG.ShultStronglyClosedTI.InvolutionCounting
