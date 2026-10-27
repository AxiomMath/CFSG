module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.Exponent

public section

namespace CFSG.ShultStronglyClosedTI.LinearChain.RootQuotientClasses

variable {G : Type*} [Group G]

theorem odd_card_orderOf_eq_two [Finite G] (hG : Even (Nat.card G)) :
    Odd (Nat.card {x : G // orderOf x = 2}) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  have hσ : Equiv.inv G ^ 2 ^ 1 = 1 := by
    ext x
    simp only [pow_one, sq, Equiv.Perm.mul_apply, Equiv.inv_apply, inv_inv, Equiv.Perm.one_apply]
  have hmod := Equiv.Perm.card_compl_support_modEq hσ
  have hcompl : (Equiv.inv G).supportᶜ =
      insert 1 (Finset.univ.filter fun x : G => orderOf x = 2) := by
    ext x
    simp only [Finset.mem_compl, Equiv.Perm.mem_support, Equiv.inv_apply, ne_eq, not_not,
      Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hx
      by_cases h1 : x = 1
      · exact Or.inl h1
      · refine Or.inr (orderOf_eq_prime ?_ h1)
        rw [sq]
        nth_rewrite 1 [← hx]
        exact inv_mul_cancel x
    · rintro (rfl | hx)
      · exact inv_one
      · exact inv_eq_self_of_orderOf_eq_two hx
  rw [hcompl, Finset.card_insert_of_notMem (by simp)] at hmod
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Nat.odd_iff]
  rw [Nat.card_eq_fintype_card] at hG
  obtain ⟨m, hm⟩ := hG
  unfold Nat.ModEq at hmod
  omega

theorem card_sup_mul_card_inf {A B : Subgroup G} (hAB : A ≤ Subgroup.normalizer (B : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) = Nat.card A * Nat.card B := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hAB
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hAB
  have he := Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient A B hAB).toEquiv
  change B.relIndex A = B.relIndex (A ⊔ B) at he
  have h1 := Subgroup.relIndex_mul_card B (A ⊔ B)
  have h2 := Subgroup.relIndex_mul_card B A
  rw [inf_eq_left.mpr le_sup_right] at h1
  rw [← h1, ← he, ← h2, inf_comm]
  ring

theorem relIndex_sup_eq_relIndex [Finite G] {A B : Subgroup G}
    (hAB : A ≤ Subgroup.normalizer (B : Set G)) : A.relIndex (A ⊔ B) = A.relIndex B := by
  have hprod := card_sup_mul_card_inf hAB
  have h1 := Subgroup.relIndex_mul_card A (A ⊔ B)
  have h2 := Subgroup.relIndex_mul_card A B
  rw [inf_eq_left.mpr le_sup_left] at h1
  have hpos : 0 < Nat.card A * Nat.card (A ⊓ B : Subgroup G) :=
    Nat.mul_pos Nat.card_pos Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc Nat.card A * Nat.card (A ⊓ B : Subgroup G) * A.relIndex (A ⊔ B)
      = Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) := by rw [← h1]; ring
    _ = Nat.card A * Nat.card B := hprod
    _ = Nat.card A * Nat.card (A ⊓ B : Subgroup G) * A.relIndex B := by rw [← h2]; ring

theorem relIndex_ne_zero_of_finite [Finite G] (S T : Subgroup G) : S.relIndex T ≠ 0 := by
  intro h0
  have hc := Subgroup.relIndex_mul_card S T
  rw [h0, zero_mul] at hc
  exact (Nat.card_pos (α := ↥T)).ne hc

theorem dvd_two_pow_factorization {q n e : ℕ} (hq : q = 2 ^ e) (hn : n ≠ 0) (h : q ∣ n) :
    q ∣ 2 ^ n.factorization 2 := by
  subst hq
  exact Nat.pow_dvd_pow 2 ((Nat.prime_two.pow_dvd_iff_le_factorization hn).mp h)

theorem mem_image_mul_left_iff {Q : Subgroup G} {u x : G} :
    x ∈ (fun y => u * y) '' (Q : Set G) ↔ u⁻¹ * x ∈ Q := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [inv_mul_cancel_left]
  · intro hx
    exact ⟨u⁻¹ * x, hx, mul_inv_cancel_left u x⟩

theorem mem_normalizer_image_mul_left_iff {Q : Subgroup G} {u g : G}
    (hg : g ∈ Subgroup.normalizer (Q : Set G)) :
    g ∈ Subgroup.normalizer ((fun y => u * y) '' (Q : Set G)) ↔ u⁻¹ * (g⁻¹ * u * g) ∈ Q := by
  constructor
  · intro hgN
    exact mem_image_mul_left_iff.mp
      ((Subgroup.mem_set_normalizer_iff''.mp hgN u).mp ⟨1, Q.one_mem, mul_one u⟩)
  · intro hy
    rw [Subgroup.mem_set_normalizer_iff'']
    intro n
    rw [mem_image_mul_left_iff, mem_image_mul_left_iff]
    have hfac : u⁻¹ * (g⁻¹ * n * g) = u⁻¹ * (g⁻¹ * u * g) * (g⁻¹ * (u⁻¹ * n) * g) := by group
    rw [hfac, Q.mul_mem_cancel_left hy]
    exact Subgroup.mem_normalizer_iff''.mp hg _

theorem le_normalizer_of_inv_conj_mem {H Q : Subgroup G}
    (hQn : ∀ k ∈ H, ∀ v ∈ Q, k⁻¹ * v * k ∈ Q) : H ≤ Subgroup.normalizer (Q : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff'']
  intro x
  refine ⟨hQn g hg x, fun hx => ?_⟩
  have h' := hQn g⁻¹ (H.inv_mem hg) _ hx
  rwa [inv_inv, show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at h'

theorem conj_mem_inf_centralizer {H Q : Subgroup G}
    (hQn : ∀ k ∈ H, ∀ v ∈ Q, k⁻¹ * v * k ∈ Q) {g x : G} (hg : g ∈ H)
    (hx : x ∈ H ⊓ Subgroup.centralizer (Q : Set G)) :
    g * x * g⁻¹ ∈ H ⊓ Subgroup.centralizer (Q : Set G) := by
  refine Subgroup.mem_inf.mpr ⟨H.mul_mem (H.mul_mem hg hx.1) (H.inv_mem hg), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hc := Subgroup.mem_centralizer_iff.mp hx.2 _ (hQn g hg v hv)
  calc v * (g * x * g⁻¹) = g * ((g⁻¹ * v * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * v * g)) * g⁻¹ := by rw [hc]
    _ = g * x * g⁻¹ * v := by group

theorem le_normalizer_of_conj_mem {H C : Subgroup G}
    (hCn : ∀ g ∈ H, ∀ x ∈ C, g * x * g⁻¹ ∈ C) : H ≤ Subgroup.normalizer (C : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨hCn g hg x, fun hx => ?_⟩
  have h' := hCn g⁻¹ (H.inv_mem hg) _ hx
  rwa [inv_inv, show g⁻¹ * (g * x * g⁻¹) * g = x by group] at h'

theorem orderOf_map_eq_two {C Q : Subgroup G} {E : Type*} [Group E] (π : ↥C →* E)
    (hπ : ∀ x y, π x = π y ↔ (x : G)⁻¹ * y ∈ Q) {x : ↥C}
    (hx2 : (x : G) ^ 2 = 1) (hxQ : (x : G) ∉ Q) : orderOf (π x) = 2 := by
  apply orderOf_eq_prime
  · rw [← map_pow, show x ^ 2 = 1 from Subtype.ext (by simpa using hx2), map_one]
  · intro h1
    rw [← map_one π, hπ] at h1
    apply hxQ
    simpa using h1

end CFSG.ShultStronglyClosedTI.LinearChain.RootQuotientClasses
