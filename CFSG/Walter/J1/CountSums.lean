module

public import CFSG.Walter.J1.Uniform
public import CFSG.Walter.J1.CosetClassify
public import CFSG.Walter.J1.HThree
public import CFSG.Walter.J1.InvCount

public section

namespace CFSG.Walter.J1

theorem sum_card_filter_comm {α β : Type*} (X : Finset α) (U : Finset β) (R : α → β → Prop)
    [∀ a b, Decidable (R a b)] :
    ∑ u ∈ U, (X.filter (fun x => R x u)).card = ∑ x ∈ X, (U.filter (fun u => R x u)).card := by
  simp only [Finset.card_filter]
  exact Finset.sum_comm

namespace JankoHyp

variable {G : Type} [Group G] [Finite G] (h : JankoHyp G)

omit [Finite G] in
open Classical in
theorem invOrd_eq_card [Fintype G] (H : Subgroup G) (u : G) (k : ℕ) :
    invOrd H u k = ((Finset.univ.filter (fun d : G => d ∈ H ∧ orderOf d = k)).filter
      (fun d => u * d * u⁻¹ = d⁻¹)).card := by
  rw [invOrd, Set.ncard_eq_toFinset_card']
  congr 1
  ext d
  simp only [Set.mem_toFinset, Set.mem_ofPred_eq, Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

omit [Finite G] in
open Classical in
theorem kap_eq_card [Fintype G] (H : Subgroup G) (u : G) :
    kap H u = ((Finset.univ.filter (fun x : G => x ∈ H ∧ orderOf x = 3)).filter
      (fun x => u * x = x * u)).card := by
  rw [kap, Set.ncard_eq_toFinset_card']
  congr 1
  ext d
  simp only [Set.mem_toFinset, Set.mem_ofPred_eq, Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

omit [Finite G] in
theorem card_filter_eq_ncard [Fintype G] (H : Subgroup G) (P : G → Prop)
    [DecidablePred (fun u : G => orderOf u = 2 ∧ u ∉ H)] [DecidablePred P] :
    ((Finset.univ.filter (fun u : G => orderOf u = 2 ∧ u ∉ H)).filter P).card =
      {u : G | (orderOf u = 2 ∧ u ∉ H) ∧ P u}.ncard := by
  classical
  rw [Set.ncard_eq_toFinset_card']
  congr 1
  ext u
  simp

omit [Finite G] in
open Classical in
theorem card_filter_H_eq_ncard [Fintype G] (H : Subgroup G) (k : ℕ) :
    (Finset.univ.filter (fun x : G => x ∈ H ∧ orderOf x = k)).card =
      {x : G | x ∈ H ∧ orderOf x = k}.ncard := by
  rw [Set.ncard_eq_toFinset_card']
  congr 1
  ext u
  simp

omit [Finite G] in
open Classical in
theorem sum_invOrd_eq [Fintype G] (H : Subgroup G) (k : ℕ) :
    ∑ u ∈ Finset.univ.filter (fun u : G => orderOf u = 2 ∧ u ∉ H), invOrd H u k =
      ∑ x ∈ Finset.univ.filter (fun x : G => x ∈ H ∧ orderOf x = k),
        {u : G | (orderOf u = 2 ∧ u ∉ H) ∧ u * x * u⁻¹ = x⁻¹}.ncard := by
  simp only [invOrd_eq_card]
  rw [sum_card_filter_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  exact card_filter_eq_ncard H _

include h in
theorem ncard_commute_outside (Q : Sylow 2 G) {H : Subgroup G}
    (hH : H = Subgroup.normalizer ((Q : Subgroup G) : Set G)) {s : G} (hsH : s ∈ H)
    (hs : orderOf s = 2) :
    {u : G | (orderOf u = 2 ∧ u ∉ H) ∧ u * s * u⁻¹ = s⁻¹}.ncard = 24 := by
  subst hH
  have hsQ := mem_sylow_of_orderOf_eq_two Q hsH hs
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right (orderOf_eq_two_iff.mp hs).1
  have hQab := h.abelian_sylow Q
  set A := {u : G | orderOf u = 2 ∧ u * s = s * u}
  set B := {u : G | orderOf u = 2 ∧ u ∈ Subgroup.normalizer ((Q : Subgroup G) : Set G)}
  have hBA : B ⊆ A := by
    rintro u ⟨hu, huH⟩
    exact ⟨hu, congrArg Subtype.val (hQab.is_comm.comm ⟨u, mem_sylow_of_orderOf_eq_two Q huH hu⟩
      ⟨s, hsQ⟩)⟩
  have hset : {u : G | (orderOf u = 2 ∧ u ∉ Subgroup.normalizer ((Q : Subgroup G) : Set G)) ∧
      u * s * u⁻¹ = s⁻¹} = A \ B := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, A, B, hsinv]
    constructor
    · rintro ⟨⟨hu, huH⟩, hus⟩
      refine ⟨⟨hu, ?_⟩, fun h0 => huH h0.2⟩
      calc u * s = u * s * u⁻¹ * u := by group
        _ = s * u := by rw [hus]
    · rintro ⟨⟨hu, hus⟩, hn⟩
      exact ⟨⟨hu, fun h0 => hn ⟨hu, h0⟩⟩, by rw [hus, mul_inv_cancel_right]⟩
  rw [hset, Set.ncard_sdiff hBA, h.ncard_commute_involution hs, h.ncard_involutions_normalizer Q]

include h in
theorem ncard_inv_outside (Q : Sylow 2 G) {H : Subgroup G}
    (hH : H = Subgroup.normalizer ((Q : Subgroup G) : Set G)) {x : G} (hxH : x ∈ H)
    (hx : orderOf x = 3 ∨ orderOf x = 6 ∨ orderOf x = 7) :
    {u : G | (orderOf u = 2 ∧ u ∉ H) ∧ u * x * u⁻¹ = x⁻¹} =
      {u : G | orderOf u = 2 ∧ u * x * u⁻¹ = x⁻¹} := by
  subst hH
  ext u
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hu, -⟩, hux⟩
    exact ⟨hu, hux⟩
  · rintro ⟨hu, hux⟩
    exact ⟨⟨hu, fun huH => h.not_mem_of_inv Q hu huH hxH hx hux⟩, hux⟩

omit [Finite G] in
theorem inv_zpowers_iff (x u : G) :
    (∀ z ∈ Subgroup.zpowers x, u * z * u⁻¹ = z⁻¹) ↔ u * x * u⁻¹ = x⁻¹ := by
  constructor
  · intro hz
    exact hz x (Subgroup.mem_zpowers x)
  · rintro hx _ ⟨k, rfl⟩
    change u * x ^ k * u⁻¹ = (x ^ k)⁻¹
    rw [← conj_zpow, hx, inv_zpow]

omit [Finite G] in
theorem mem_centralizer_zpowers_iff (x u : G) :
    u ∈ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) ↔ u * x = x * u := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro hz
    exact (hz x (Subgroup.mem_zpowers x)).symm
  · rintro hx _ ⟨k, rfl⟩
    exact (Commute.zpow_left (Commute.symm hx) k).eq

include h in
open Classical in
theorem sum_invOrd_two [Fintype G] (Q : Sylow 2 G) {H : Subgroup G}
    (hH : H = Subgroup.normalizer ((Q : Subgroup G) : Set G)) :
    ∑ u ∈ Finset.univ.filter (fun u : G => orderOf u = 2 ∧ u ∉ H), invOrd H u 2 = 168 := by
  rw [sum_invOrd_eq, Finset.sum_congr rfl (fun x hx => h.ncard_commute_outside Q hH
    (Finset.mem_filter.mp hx).2.1 (Finset.mem_filter.mp hx).2.2), Finset.sum_const, smul_eq_mul,
    card_filter_H_eq_ncard]
  subst hH
  have : {x : G | x ∈ Subgroup.normalizer ((Q : Subgroup G) : Set G) ∧ orderOf x = 2}.ncard =
      7 := by
    rw [← h.ncard_involutions_normalizer Q]
    congr 1
    ext x
    simp only [Set.mem_ofPred_eq]
    exact and_comm
  rw [this]

include h in
open Classical in
theorem sum_invOrd_six [Fintype G] (Q : Sylow 2 G) {H : Subgroup G}
    (hH : H = Subgroup.normalizer ((Q : Subgroup G) : Set G)) :
    ∑ u ∈ Finset.univ.filter (fun u : G => orderOf u = 2 ∧ u ∉ H), invOrd H u 6 = 336 := by
  have hterm : ∀ x ∈ Finset.univ.filter (fun x : G => x ∈ H ∧ orderOf x = 6),
      {u : G | (orderOf u = 2 ∧ u ∉ H) ∧ u * x * u⁻¹ = x⁻¹}.ncard = 6 := fun x hx => by
    rw [h.ncard_inv_outside Q hH (Finset.mem_filter.mp hx).2.1
      (Or.inr (Or.inl (Finset.mem_filter.mp hx).2.2)),
      h.ncard_inv_six (Finset.mem_filter.mp hx).2.2]
  rw [sum_invOrd_eq, Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul,
    card_filter_H_eq_ncard]
  subst hH
  rw [h.ncard_orderOf_six Q]

include h in
open Classical in
theorem sum_invOrd_three [Fintype G] (Q : Sylow 2 G) {H : Subgroup G}
    (hH : H = Subgroup.normalizer ((Q : Subgroup G) : Set G)) {d : ℕ}
    (hd : ∀ X : Subgroup G, Nat.card X = 3 →
      {u : G | orderOf u = 2 ∧ ∀ x ∈ X, u * x * u⁻¹ = x⁻¹}.ncard = 6 * d) :
    ∑ u ∈ Finset.univ.filter (fun u : G => orderOf u = 2 ∧ u ∉ H), invOrd H u 3 =
      56 * (6 * d) := by
  have hterm : ∀ x ∈ Finset.univ.filter (fun x : G => x ∈ H ∧ orderOf x = 3),
      {u : G | (orderOf u = 2 ∧ u ∉ H) ∧ u * x * u⁻¹ = x⁻¹}.ncard = 6 * d := fun x hx => by
    rw [h.ncard_inv_outside Q hH (Finset.mem_filter.mp hx).2.1
      (Or.inl (Finset.mem_filter.mp hx).2.2)]
    have h1 := hd (Subgroup.zpowers x) (by rw [Nat.card_zpowers, (Finset.mem_filter.mp hx).2.2])
    simp only [inv_zpowers_iff] at h1
    exact h1
  rw [sum_invOrd_eq, Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul,
    card_filter_H_eq_ncard]
  subst hH
  rw [h.ncard_orderOf_three Q]

include h in
open Classical in
theorem sum_invOrd_seven [Fintype G] (Q : Sylow 2 G) {H : Subgroup G}
    (hH : H = Subgroup.normalizer ((Q : Subgroup G) : Set G)) {y₀ : G} (hy₀H : y₀ ∈ H)
    (hy₀ : orderOf y₀ = 7) :
    ∑ u ∈ Finset.univ.filter (fun u : G => orderOf u = 2 ∧ u ∉ H), invOrd H u 7 =
      48 * {u : G | orderOf u = 2 ∧ u * y₀ * u⁻¹ = y₀⁻¹}.ncard := by
  have hterm : ∀ x ∈ Finset.univ.filter (fun x : G => x ∈ H ∧ orderOf x = 7),
      {u : G | (orderOf u = 2 ∧ u ∉ H) ∧ u * x * u⁻¹ = x⁻¹}.ncard =
        {u : G | orderOf u = 2 ∧ u * y₀ * u⁻¹ = y₀⁻¹}.ncard := fun x hx => by
    rw [h.ncard_inv_outside Q hH (Finset.mem_filter.mp hx).2.1
      (Or.inr (Or.inr (Finset.mem_filter.mp hx).2.2))]
    subst hH
    exact h.ncard_inv_seven_eq Q (Finset.mem_filter.mp hx).2.1 hy₀H
      (Finset.mem_filter.mp hx).2.2 hy₀
  rw [sum_invOrd_eq, Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul,
    card_filter_H_eq_ncard]
  subst hH
  rw [h.ncard_orderOf_seven Q]

include h in
theorem ncard_commute_three_outside (Q : Sylow 2 G) {H : Subgroup G}
    (hH : H = Subgroup.normalizer ((Q : Subgroup G) : Set G)) {d : ℕ}
    (hd : ∀ X : Subgroup G, Nat.card X = 3 →
      {u : G | orderOf u = 2 ∧ u ∈ Subgroup.centralizer (X : Set G)}.ncard = 2 * d - 1)
    {x : G} (hxH : x ∈ H) (hx : orderOf x = 3) :
    {u : G | (orderOf u = 2 ∧ u ∉ H) ∧ u * x = x * u}.ncard = 2 * d - 2 := by
  subst hH
  set H := Subgroup.normalizer ((Q : Subgroup G) : Set G)
  set A := {u : G | orderOf u = 2 ∧ u * x = x * u}
  set B := {u : G | orderOf u = 2 ∧ u ∈ H ∧ u * x = x * u}
  have hA : A.ncard = 2 * d - 1 := by
    have h1 := hd (Subgroup.zpowers x) (by rw [Nat.card_zpowers, hx])
    simp only [mem_centralizer_zpowers_iff] at h1
    exact h1
  have hB : B.ncard = 1 := by
    have hK := h.card_inf_centralizer_three Q hxH hx
    have : B = (((Q : Subgroup G) ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G) \
        {1} := by
      ext u
      simp only [Set.mem_ofPred_eq, Set.mem_sdiff, SetLike.mem_coe, Subgroup.mem_inf,
        Subgroup.mem_centralizer_singleton_iff, Set.mem_singleton_iff, B]
      constructor
      · rintro ⟨hu, huH, hux⟩
        exact ⟨⟨mem_sylow_of_orderOf_eq_two Q huH hu, hux⟩, (orderOf_eq_two_iff.mp hu).2⟩
      · rintro ⟨⟨huQ, hux⟩, hu1⟩
        exact ⟨orderOf_eq_two_iff.mpr ⟨h.mul_self_of_mem_sylow' Q huQ, hu1⟩,
          Subgroup.le_normalizer huQ, hux⟩
    rw [this, Set.ncard_sdiff_singleton_of_mem (by simp), ← Nat.card_coe_set_eq,
      SetLike.coe_sort_coe, hK]
  have hBA : B ⊆ A := fun u hu => ⟨hu.1, hu.2.2⟩
  have hset : {u : G | (orderOf u = 2 ∧ u ∉ H) ∧ u * x = x * u} = A \ B := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, A, B]
    constructor
    · rintro ⟨⟨hu, huH⟩, hux⟩
      exact ⟨⟨hu, hux⟩, fun h0 => huH h0.2.1⟩
    · rintro ⟨⟨hu, hux⟩, hn⟩
      exact ⟨⟨hu, fun huH => hn ⟨hu, huH, hux⟩⟩, hux⟩
  rw [hset, Set.ncard_sdiff hBA, hA, hB]
  omega

include h in
open Classical in
theorem sum_kap [Fintype G] (Q : Sylow 2 G) {H : Subgroup G}
    (hH : H = Subgroup.normalizer ((Q : Subgroup G) : Set G)) {d : ℕ}
    (hd : ∀ X : Subgroup G, Nat.card X = 3 →
      {u : G | orderOf u = 2 ∧ u ∈ Subgroup.centralizer (X : Set G)}.ncard = 2 * d - 1) :
    ∑ u ∈ Finset.univ.filter (fun u : G => orderOf u = 2 ∧ u ∉ H), kap H u =
      56 * (2 * d - 2) := by
  simp only [kap_eq_card]
  have hterm : ∀ x ∈ Finset.univ.filter (fun x : G => x ∈ H ∧ orderOf x = 3),
      ((Finset.univ.filter (fun u : G => orderOf u = 2 ∧ u ∉ H)).filter
        (fun u => u * x = x * u)).card = 2 * d - 2 := fun x hx => by
    rw [card_filter_eq_ncard H (fun u => u * x = x * u)]
    exact h.ncard_commute_three_outside Q hH hd (Finset.mem_filter.mp hx).2.1
      (Finset.mem_filter.mp hx).2.2
  rw [sum_card_filter_comm, Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul,
    card_filter_H_eq_ncard]
  subst hH
  rw [h.ncard_orderOf_three Q]

end JankoHyp

end CFSG.Walter.J1
