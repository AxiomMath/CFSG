module

public import CFSG.Walter.J1.CountSums
public import CFSG.Walter.J1.Seven

public section

namespace CFSG.Walter.J1

namespace JankoHyp

variable {G : Type} [Group G] [Finite G] (h : JankoHyp G)

include h in
theorem ncard_commute_inv_seven (Q : Sylow 2 G) {H : Subgroup G}
    (hH : H = Subgroup.normalizer ((Q : Subgroup G) : Set G)) {x y : G} (hxH : x ∈ H)
    (hx : orderOf x = 3) (hyH : y ∈ H) (hy : orderOf y = 7) :
    {u : G | (orderOf u = 2 ∧ u ∉ H) ∧ (u * x = x * u ∧ u * y * u⁻¹ = y⁻¹)}.ncard =
      if x * y * x⁻¹ ∈ Subgroup.zpowers y then
        (if {u : G | orderOf u = 2 ∧ u * y * u⁻¹ = y⁻¹}.ncard = 0 then 0 else 1) else 0 := by
  subst hH
  set H := Subgroup.normalizer ((Q : Subgroup G) : Set G)
  have hy1 : y ≠ 1 := fun h0 => by rw [h0, orderOf_one] at hy; omega
  have hyc : Nat.Coprime (orderOf y) 30 := by rw [hy]; norm_num
  split_ifs with hxy hr
  ·
    rw [Set.ncard_eq_zero (Set.toFinite _), Set.eq_empty_iff_forall_notMem]
    rintro u ⟨⟨hu, -⟩, -, huy⟩
    rw [Set.ncard_eq_zero (Set.toFinite _), Set.eq_empty_iff_forall_notMem] at hr
    exact hr u ⟨hu, huy⟩
  ·
    obtain ⟨t', ht', ht'y⟩ : ∃ t', orderOf t' = 2 ∧ t' * y * t'⁻¹ = y⁻¹ := by
      by_contra hn
      push Not at hn
      apply hr
      rw [Set.ncard_eq_zero (Set.toFinite _), Set.eq_empty_iff_forall_notMem]
      rintro u ⟨hu, huy⟩
      exact hn u hu huy
    have := h.ncard_inverting_commute hy1 hyc ht' ht'y hx hxy
    rw [← this]
    congr 1
    ext u
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hu, -⟩, hux, huy⟩
      exact ⟨⟨hu, huy⟩, hux⟩
    · rintro ⟨⟨hu, huy⟩, hux⟩
      exact ⟨⟨hu, fun huH => h.not_mem_of_inv Q hu huH hyH (Or.inr (Or.inr hy)) huy⟩, hux, huy⟩
  ·
    rw [Set.ncard_eq_zero (Set.toFinite _), Set.eq_empty_iff_forall_notMem]
    rintro u ⟨⟨hu, huH⟩, hux, huy⟩
    have hyD : y ∈ cosetD H u := mem_cosetD.mpr ⟨hyH, by rw [huy]; exact H.inv_mem hyH⟩
    have hxD : x ∈ cosetD H u := mem_cosetD.mpr ⟨hxH, by rw [hux, mul_inv_cancel_right]; exact hxH⟩
    exact hxy (h.conj_mem_zpowers_of_seven Q huH hyD hy hxD)

include h in
open Classical in
theorem sum_kap_mul_invOrd_seven [Fintype G] (Q : Sylow 2 G) {H : Subgroup G}
    (hH : H = Subgroup.normalizer ((Q : Subgroup G) : Set G)) {y₀ : G} (hy₀H : y₀ ∈ H)
    (hy₀ : orderOf y₀ = 7) :
    ∑ u ∈ Finset.univ.filter (fun u : G => orderOf u = 2 ∧ u ∉ H), kap H u * invOrd H u 7 =
      672 * (if {u : G | orderOf u = 2 ∧ u * y₀ * u⁻¹ = y₀⁻¹}.ncard = 0 then 0 else 1) := by
  set X₃ := Finset.univ.filter (fun x : G => x ∈ H ∧ orderOf x = 3)
  set X₇ := Finset.univ.filter (fun x : G => x ∈ H ∧ orderOf x = 7)
  set U := Finset.univ.filter (fun u : G => orderOf u = 2 ∧ u ∉ H)
  set e := if {u : G | orderOf u = 2 ∧ u * y₀ * u⁻¹ = y₀⁻¹}.ncard = 0 then 0 else 1
  have hprod : ∀ u : G, kap H u * invOrd H u 7 =
      ((X₃ ×ˢ X₇).filter (fun p : G × G => u * p.1 = p.1 * u ∧
        u * p.2 * u⁻¹ = p.2⁻¹)).card := by
    intro u
    rw [kap_eq_card, invOrd_eq_card, ← Finset.card_product]
    congr 1
    ext ⟨a, b⟩
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, X₃, X₇]
    tauto
  simp only [hprod]
  rw [sum_card_filter_comm]
  have hterm : ∀ p ∈ X₃ ×ˢ X₇, (U.filter (fun u => u * p.1 = p.1 * u ∧
      u * p.2 * u⁻¹ = p.2⁻¹)).card =
      if p.1 * p.2 * p.1⁻¹ ∈ Subgroup.zpowers p.2 then e else 0 := by
    rintro ⟨x, y⟩ hp
    rw [Finset.mem_product] at hp
    obtain ⟨hx, hy⟩ := hp
    simp only [X₃, X₇, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    show ((Finset.univ.filter (fun u : G => orderOf u = 2 ∧ u ∉ H)).filter
      (fun u => u * x = x * u ∧ u * y * u⁻¹ = y⁻¹)).card =
        if x * y * x⁻¹ ∈ Subgroup.zpowers y then e else 0
    rw [card_filter_eq_ncard H (fun u => u * x = x * u ∧ u * y * u⁻¹ = y⁻¹),
      h.ncard_commute_inv_seven Q hH hx.1 hx.2 hy.1 hy.2]
    subst hH
    simp only [e, h.ncard_inv_seven_eq Q hy.1 hy₀H hy.2 hy₀]
  rw [Finset.sum_congr rfl hterm, Finset.sum_product, Finset.sum_comm]
  have hinner : ∀ y ∈ X₇, (∑ x ∈ X₃, if x * y * x⁻¹ ∈ Subgroup.zpowers y then e else 0) =
      14 * e := by
    intro y hy
    simp only [X₇, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
    congr 1
    rw [Finset.filter_filter]
    have := h.ncard_normalizer_three Q (hH ▸ hy.1) hy.2
    rw [Set.ncard_eq_toFinset_card'] at this
    rw [← this]
    congr 1
    ext x
    subst hH
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset,
      Set.mem_ofPred_eq]
    tauto
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul, card_filter_H_eq_ncard]
  subst hH
  rw [h.ncard_orderOf_seven Q]
  ring

end JankoHyp

end CFSG.Walter.J1
