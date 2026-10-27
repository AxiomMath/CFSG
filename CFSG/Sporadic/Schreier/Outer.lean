module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingImagePairs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSmallOrders

public section

namespace CFSG.Sporadic.Schreier

open CFSG.ComponentClassification.CatalogueSchreierAlternating
open CFSG.ComponentClassification.OuterAutomorphisms

variable {G : Type*} [Group G]

theorem mul_ne_mul_of_orderOf_commutator {a b : G} {s : ℕ}
    (h : orderOf (a * b * a⁻¹ * b⁻¹) = s) (hs : s ≠ 1) : a * b ≠ b * a := by
  intro hab
  rw [hab, mul_inv_cancel_right, mul_inv_cancel, orderOf_one] at h
  exact hs h.symm

theorem center_eq_bot_of_simple (hs : IsSimpleGroup G) {a b : G} (hab : a * b ≠ b * a) :
    Subgroup.center G = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · exact h
  · exact absurd (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a) hab

theorem card_inner_of_center_eq_bot (hc : Subgroup.center G = ⊥) :
    Nat.card (inner G) = Nat.card G := by
  have hinj : Function.Injective (MulAut.conj : G →* MulAut G) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply le_antisymm _ bot_le
    intro x hx
    have hcentral : x ∈ Subgroup.center G := by
      apply Subgroup.mem_center_iff.mpr
      intro y
      have hconj := congrArg (fun f : MulAut G => f y) hx
      change x * y * x⁻¹ = y at hconj
      have heq := congrArg (fun z : G => z * x) hconj
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using heq.symm
    rwa [hc] at hcentral
  change Nat.card (MulAut.conj : G →* MulAut G).range = _
  rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]

theorem outer_card_mul_le [Finite G] (hs : IsSimpleGroup G) {a b : G}
    (hgen : Subgroup.closure ({a, b} : Set G) = ⊤) (hab : a * b ≠ b * a) :
    Nat.card (Outer G) * Nat.card G ≤ Nat.card (ImagePairOrders a b) := by
  have haut := automorphism_card_le_image_pairs a b hgen
  have hquot := (inner G).card_eq_card_quotient_mul_card_subgroup
  rw [card_inner_of_center_eq_bot (center_eq_bot_of_simple hs hab)] at hquot
  change Nat.card (MulAut G ⧸ inner G) * Nat.card G ≤ _
  rw [← hquot]
  exact haut

theorem outer_card_le_of_mulAut_card [Finite G] (hs : IsSimpleGroup G) {a b : G}
    (hab : a * b ≠ b * a) {k : ℕ} (hk : Nat.card (MulAut G) ≤ k * Nat.card G)
    (hN0 : 0 < Nat.card G) : Nat.card (Outer G) ≤ k := by
  have hquot := (inner G).card_eq_card_quotient_mul_card_subgroup
  rw [card_inner_of_center_eq_bot (center_eq_bot_of_simple hs hab)] at hquot
  change Nat.card (MulAut G ⧸ inner G) ≤ k
  rw [hquot] at hk
  exact Nat.le_of_mul_le_mul_right hk hN0

theorem card_imagePairOrders {a b : G} {mx my r s : ℕ} (ha : orderOf a = mx)
    (hb : orderOf b = my) (hab : orderOf (a * b) = r) (hc : orderOf (a * b * a⁻¹ * b⁻¹) = s) :
    Nat.card (ImagePairOrders a b) = Nat.card {p : G × G // orderOf p.1 = mx ∧
      orderOf p.2 = my ∧ orderOf (p.1 * p.2) = r ∧ orderOf (p.1 * p.2 * p.1⁻¹ * p.2⁻¹) = s} := by
  rw [ImagePairOrders, ha, hb, hab, hc]
  rfl

theorem outer_card_le_of_counts [Finite G] (hs : IsSimpleGroup G) {a b : G}
    (hgen : Subgroup.closure ({a, b} : Set G) = ⊤) {mx my r s N T k : ℕ} (ha : orderOf a = mx)
    (hb : orderOf b = my) (hab : orderOf (a * b) = r) (hc : orderOf (a * b * a⁻¹ * b⁻¹) = s)
    (hs1 : s ≠ 1) (hN : Nat.card G = N) (hN0 : 0 < N)
    (hT : Nat.card {p : G × G // orderOf p.1 = mx ∧ orderOf p.2 = my ∧
      orderOf (p.1 * p.2) = r ∧ orderOf (p.1 * p.2 * p.1⁻¹ * p.2⁻¹) = s} = T)
    (hk : T ≤ k * N) : Nat.card (Outer G) ≤ k := by
  have h := outer_card_mul_le hs hgen (mul_ne_mul_of_orderOf_commutator hc hs1)
  rw [card_imagePairOrders ha hb hab hc, hT, hN] at h
  exact Nat.le_of_mul_le_mul_right (h.trans hk) hN0

theorem outer_schreier_of_counts [Finite G] (hs : IsSimpleGroup G) {a b : G}
    (hgen : Subgroup.closure ({a, b} : Set G) = ⊤) {mx my r s N T k : ℕ} (ha : orderOf a = mx)
    (hb : orderOf b = my) (hab : orderOf (a * b) = r) (hc : orderOf (a * b * a⁻¹ * b⁻¹) = s)
    (hs1 : s ≠ 1) (hN : Nat.card G = N) (hN0 : 0 < N)
    (hT : Nat.card {p : G × G // orderOf p.1 = mx ∧ orderOf p.2 = my ∧
      orderOf (p.1 * p.2) = r ∧ orderOf (p.1 * p.2 * p.1⁻¹ * p.2⁻¹) = s} = T)
    (hk : T ≤ k * N) (hk4 : k ≤ 4) :
    Nat.card (Outer G) ≤ k ∧ IsMulCommutative (Outer G) ∧ Group.IsSolvable (Outer G) := by
  have h := outer_card_le_of_counts hs hgen ha hb hab hc hs1 hN hN0 hT hk
  exact ⟨h, commutative_of_card_le_four (h.trans hk4), solvable_of_card_le_four (h.trans hk4)⟩

end CFSG.Sporadic.Schreier
