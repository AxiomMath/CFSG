module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.PairInvolutionFixedFieldOrbit

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.FixedPointModel

open CFSG.ShultStronglyClosedTI
open CFSG.ShultStronglyClosedTI.PairInvolutionFixedField
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

theorem card_pairs_of_fibers {α β : Type*} [Finite α] (S : Set α) (fp : α → β) (c : ℕ)
    (hfiber : ∀ a ∈ S, Nat.card {b // b ∈ S ∧ fp b = fp a} = c)
    (P : α → α → Prop) (hP : ∀ a ∈ S, ∀ b ∈ S, P a b ↔ (fp b ≠ fp a ∨ b = a)) :
    Nat.card {p : α × α // p.1 ∈ S ∧ p.2 ∈ S ∧ P p.1 p.2} =
      Nat.card S * (Nat.card S - c + 1) := by
  classical
  let := Fintype.ofFinite α
  let T := S.toFinset
  have hcardS : Nat.card S = T.card := by
    rw [Nat.card_eq_fintype_card, Set.toFinset_card]
  have hpairs : Nat.card {p : α × α // p.1 ∈ S ∧ p.2 ∈ S ∧ P p.1 p.2} =
      ((T ×ˢ T).filter fun p => P p.1 p.2).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext p
    simp [T, and_assoc]
  have hrow : ∀ a ∈ T, (T.filter fun b => P a b).card = T.card - c + 1 := by
    intro a ha
    have haS : a ∈ S := Set.mem_toFinset.mp ha
    have hsplit : T.filter (fun b => P a b) = insert a (T.filter fun b => fp b ≠ fp a) := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hb, hPab⟩
        rcases (hP a haS b (Set.mem_toFinset.mp hb)).mp hPab with hne | heq
        · exact Or.inr ⟨hb, hne⟩
        · exact Or.inl heq
      · rintro (rfl | ⟨hb, hne⟩)
        · exact ⟨ha, (hP b haS b haS).mpr (Or.inr rfl)⟩
        · exact ⟨hb, (hP a haS b (Set.mem_toFinset.mp hb)).mpr (Or.inl hne)⟩
    have hnot : a ∉ T.filter fun b => fp b ≠ fp a := by simp
    have hfib : (T.filter fun b => fp b = fp a).card = c := by
      rw [← hfiber a haS, Nat.card_eq_fintype_card, Fintype.card_subtype]
      congr 1
      ext b
      simp [T]
    have hsum := Finset.card_filter_add_card_filter_not (s := T) (fun b => fp b = fp a)
    rw [hsplit, Finset.card_insert_of_notMem hnot]
    simp only [ne_eq] at hsum ⊢
    omega
  rw [hpairs, hcardS, Finset.card_filter, Finset.sum_product,
    Finset.sum_const_nat (m := T.card - c + 1)]
  intro a ha
  rw [← Finset.card_filter]
  exact hrow a ha

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem class_commute_of_common_fixed {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) {Q : Subgroup G}
    (hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a)
    (hQclass : (Q : Set G) \ {1} = conjugacyWithin H z) {a b : G}
    (ha : a ∈ involutionPointClass z) (hb : b ∈ involutionPointClass z)
    {ω : rightCosetSpace H} (haω : rightCosetTranslate H ω a = ω)
    (hbω : rightCosetTranslate H ω b = ω) : Commute a b := by
  obtain ⟨g, rfl⟩ := exists_rightCosetMk ω
  have hmem : ∀ s ∈ involutionPointClass z, rightCosetTranslate H (rightCosetMk H g) s =
      rightCosetMk H g → g * s * g⁻¹ ∈ Q := by
    intro s hs hsω
    have hsH : g * s * g⁻¹ ∈ H := (translate_mk_fixed_iff H g s).mp hsω
    have hsD : g * s * g⁻¹ ∈ involutionPointClass z := by
      simpa only [inv_inv] using conj_mem_pointClass hs g⁻¹
    have hsQ : g * s * g⁻¹ ∈ (Q : Set G) \ {1} := by
      rw [← class_inter_point h hQclass]
      exact ⟨hsD, hsH⟩
    exact hsQ.1
  have hcomm := hQab _ (hmem a ha haω) _ (hmem b hb hbω)
  have h' : g * (a * b) * g⁻¹ = g * (b * a) * g⁻¹ := by
    calc g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      _ = (g * b * g⁻¹) * (g * a * g⁻¹) := hcomm
      _ = g * (b * a) * g⁻¹ := by group
  exact mul_left_cancel (mul_right_cancel h')

theorem class_product_odd_iff {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    {Q : Subgroup G} (hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a)
    (hQclass : (Q : Set G) \ {1} = conjugacyWithin H z)
    (heven : ∀ r s : G, r ∈ involutionPointClass z → s ∈ involutionPointClass z →
      Even (orderOf (r * s)) → Commute r s)
    {a b : G} (ha : a ∈ involutionPointClass z) (hb : b ∈ involutionPointClass z)
    {ωa ωb : rightCosetSpace H} (hωa : rightCosetTranslate H ωa a = ωa)
    (hωb : rightCosetTranslate H ωb b = ωb) :
    Odd (orderOf (a * b)) ↔ (ωb ≠ ωa ∨ b = a) := by
  have haa : a * a = 1 :=
    mul_self_eq_one_of_orderOf_eq_two (order_two_of_mem_pointClass h.distinguished_order ha)
  have hbb : b * b = 1 :=
    mul_self_eq_one_of_orderOf_eq_two (order_two_of_mem_pointClass h.distinguished_order hb)
  constructor
  · intro hodd
    by_contra hcon
    push Not at hcon
    obtain ⟨hω, hba⟩ := hcon
    have hcomm : Commute a b := class_commute_of_common_fixed h hQab hQclass ha hb hωa (hω ▸ hωb)
    have hsq : (a * b) ^ 2 = 1 := by
      calc (a * b) ^ 2 = a * (b * a) * b := by rw [pow_two]; simp only [mul_assoc]
        _ = a * (a * b) * b := by rw [hcomm.eq]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [haa, hbb, one_mul]
    have hdvd : orderOf (a * b) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
    have hone : orderOf (a * b) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
      · exact h1
      · rw [h2] at hodd
        exact absurd hodd (by decide)
    have hab1 : a * b = 1 := orderOf_eq_one_iff.mp hone
    apply hba
    calc b = a * a * b := by rw [haa, one_mul]
      _ = a * (a * b) := by group
      _ = a := by rw [hab1, mul_one]
  · rintro (hne | rfl)
    · by_contra hnot
      have hcomm := heven a b ha hb (Nat.not_odd_iff_even.mp hnot)
      exact hne (class_fixed_unique h hb hωb (class_fixed_of_commute h ha hcomm hωa))
    · rw [haa, orderOf_one]
      exact odd_one

omit [Finite G] in
theorem class_fiber_card {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    {Q : Subgroup G} (hQclass : (Q : Set G) \ {1} = conjugacyWithin H z) {u : G}
    (horbit : {omega : rightCosetSpace H | ∃ y ∈ Subgroup.centralizer ({u} : Set G),
        rightCosetTranslate H (rightCosetMk H 1) y = omega} =
      {omega : rightCosetSpace H | rightCosetTranslate H omega u = omega})
    {γ : rightCosetSpace H} (hγ : rightCosetTranslate H γ u = γ) :
    Nat.card {s : G // s ∈ involutionPointClass z ∩
        (Subgroup.centralizer ({u} : Set G) : Set G) ∧ rightCosetTranslate H γ s = γ} =
      Nat.card (Q ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) - 1 := by
  let Y := Subgroup.centralizer ({u} : Set G)
  let D := involutionPointClass z ∩ (Y : Set G)
  have hconjD : ∀ s ∈ D, ∀ a ∈ Y, a⁻¹ * s * a ∈ D := fun s hs a ha =>
    ⟨conj_mem_pointClass hs.1 a, Y.mul_mem (Y.mul_mem (Y.inv_mem ha) hs.2) ha⟩
  have hbase : Nat.card {s : G // s ∈ D ∧
      rightCosetTranslate H (rightCosetMk H 1) s = rightCosetMk H 1} =
      Nat.card ↥(((Q ⊓ Y : Subgroup G) : Set G) \ {1}) := by
    apply Nat.card_congr
    refine Equiv.ofBijective (fun s => ⟨(s : G), ?_⟩) ⟨?_, ?_⟩
    · have hsQ : (s : G) ∈ (Q : Set G) \ {1} := by
        rw [← class_inter_point h hQclass]
        exact ⟨s.2.1.1, (translate_base_iff H _).mp s.2.2⟩
      exact ⟨⟨hsQ.1, s.2.1.2⟩, hsQ.2⟩
    · intro s₁ s₂ hs
      have hs' := congrArg Subtype.val hs
      exact Subtype.ext hs'
    · rintro ⟨w, hw⟩
      have hwD : w ∈ involutionPointClass z ∩ (H : Set G) := by
        rw [class_inter_point h hQclass]
        exact ⟨hw.1.1, hw.2⟩
      exact ⟨⟨w, ⟨hwD.1, hw.1.2⟩, (translate_base_iff H w).mpr hwD.2⟩, rfl⟩
  rw [← card_diff_one, ← hbase]
  have hγorbit : γ ∈ {omega : rightCosetSpace H | ∃ y ∈ Y,
      rightCosetTranslate H (rightCosetMk H 1) y = omega} := by
    rw [horbit]
    exact hγ
  obtain ⟨y, hy, hyγ⟩ := hγorbit
  apply Nat.card_congr
  refine
    { toFun := fun s => ⟨y * s * y⁻¹, by
          simpa only [inv_inv] using hconjD s.1 s.2.1 y⁻¹ (Y.inv_mem hy), ?_⟩
      invFun := fun s => ⟨y⁻¹ * s * y, hconjD s.1 s.2.1 y hy, ?_⟩
      left_inv := fun s => Subtype.ext (by group)
      right_inv := fun s => Subtype.ext (by group) }
  · have hs := s.2.2
    change rightCosetTranslate H (rightCosetMk H 1) (y * s * y⁻¹) = rightCosetMk H 1
    rw [← rightCosetTranslate_mul, ← rightCosetTranslate_mul, hyγ, hs, ← hyγ,
      rightCosetTranslate_mul, mul_inv_cancel, rightCosetTranslate_one]
  · have hs := s.2.2
    change rightCosetTranslate H γ (y⁻¹ * s * y) = γ
    rw [← hyγ, rightCosetTranslate_mul,
      show y * (y⁻¹ * (s : G) * y) = s * y by group, ← rightCosetTranslate_mul, hs]

theorem odd_product_pair_count {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    {Q : Subgroup G} (hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a)
    (hQclass : (Q : Set G) \ {1} = conjugacyWithin H z)
    (heven : ∀ r s : G, r ∈ involutionPointClass z → s ∈ involutionPointClass z →
      Even (orderOf (r * s)) → Commute r s) {u : G}
    (horbit : {omega : rightCosetSpace H | ∃ y ∈ Subgroup.centralizer ({u} : Set G),
        rightCosetTranslate H (rightCosetMk H 1) y = omega} =
      {omega : rightCosetSpace H | rightCosetTranslate H omega u = omega}) :
    Nat.card {p : G × G // p.1 ∈ involutionPointClass z ∩
        (Subgroup.centralizer ({u} : Set G) : Set G) ∧
      p.2 ∈ involutionPointClass z ∩ (Subgroup.centralizer ({u} : Set G) : Set G) ∧
      Odd (orderOf (p.1 * p.2))} =
      Nat.card ↥(involutionPointClass z ∩ (Subgroup.centralizer ({u} : Set G) : Set G)) *
        (Nat.card ↥(involutionPointClass z ∩ (Subgroup.centralizer ({u} : Set G) : Set G)) -
          (Nat.card (Q ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) - 1) + 1) := by
  classical
  let Y := Subgroup.centralizer ({u} : Set G)
  let D := involutionPointClass z
  let fp : G → rightCosetSpace H := fun s =>
    if hs : s ∈ D then Classical.choose (class_fixed_exists h hs) else rightCosetMk H 1
  have hfp : ∀ s ∈ D, rightCosetTranslate H (fp s) s = fp s := by
    intro s hs
    simp only [fp, dite_eq_left hs]
    exact Classical.choose_spec (class_fixed_exists h hs)
  have hfpu : ∀ s ∈ D ∩ (Y : Set G), rightCosetTranslate H (fp s) u = fp s := fun s hs =>
    class_fixed_of_commute h hs.1 (Subgroup.mem_centralizer_singleton_iff.mp hs.2) (hfp s hs.1)
  apply card_pairs_of_fibers _ fp _ _ _ fun a ha b hb =>
    class_product_odd_iff h hQab hQclass heven ha.1 hb.1 (hfp a ha.1) (hfp b hb.1)
  intro a ha
  rw [← class_fiber_card h hQclass horbit (hfpu a ha)]
  apply Nat.card_congr
  refine Equiv.subtypeEquivRight fun b => and_congr_right fun hb => ?_
  constructor
  · intro hab
    rw [← hab]
    exact hfp b hb.1
  · intro hb'
    exact class_fixed_unique h hb.1 (hfp b hb.1) hb'

end CFSG.ShultStronglyClosedTI.FixedPointModel
