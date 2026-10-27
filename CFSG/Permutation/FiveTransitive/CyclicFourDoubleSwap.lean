module

public import CFSG.Permutation.FiveTransitive.CyclicFourFreeCoset
public import CFSG.Permutation.FiveTransitive.NormalizerSevenOrbitCount
public import Mathlib.GroupTheory.GroupAction.FixedPoints

public section

namespace CFSG

open scoped Classical

namespace FiveTransitive.CyclicFourDoubleSwap

open MulAction NormalizerFixedComplement

theorem even_orbit_card
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (hQ : Nat.card Q = 4)
    (hseven : Nat.card (fixedPoints Q X) = 7)
    (hfree : ∀ (q : Q) (t : X), t ∉ fixedPoints Q X → q • t = t → q = 1)
    (hdiv : 8 ∣ Nat.card X - 7) :
    Even (Nat.card (orbitRel.Quotient (Inside Q) (Domain (X := X) Q))) := by
  have hI : Nat.card (Inside Q) = 4 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe Q.le_normalizer).toEquiv).trans hQ
  have he := FreeComplementOrbitCount.card_eq_mul_orbits (free_inside Q hfree)
  rw [card_domain Q, hI] at he
  have hs : (fixedPoints Q X).ncard = 7 := by simpa only [Nat.card_coe_set_eq] using hseven
  rw [hs] at he
  obtain ⟨k, hk⟩ := hdiv
  refine ⟨k, ?_⟩
  omega

private theorem outside_le_four
    {G X : Type*} [Group G] [Finite X] [MulAction G X]
    (hmax : ∀ u : G, orderOf u = 2 → (fixedBy X u).ncard ≤ 7)
    (Q : Subgroup G) (u : G) (hu : orderOf u = 2)
    (hlocal : (fixedBy X u ∩ fixedPoints Q X).ncard = 3) :
    (fixedBy X u \ fixedPoints Q X).ncard ≤ 4 := by
  have he : fixedBy X u \ fixedPoints Q X =
      fixedBy X u \ (fixedBy X u ∩ fixedPoints Q X) := by ext t; simp only [Set.mem_sdiff, Set.mem_inter_iff]; tauto
  rw [he, Set.ncard_sdiff Set.inter_subset_left, hlocal]
  have hh := hmax u hu
  omega

theorem counts
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (hmax : ∀ u : G, orderOf u = 2 → (fixedBy X u).ncard ≤ 7)
    (Q : Subgroup G) (hQ : Nat.card Q = 4)
    (hseven : Nat.card (fixedPoints Q X) = 7)
    (hfree : ∀ (q : Q) (t : X), t ∉ fixedPoints Q X → q • t = t → q = 1)
    (heven : Even (Nat.card (orbitRel.Quotient (Inside Q) (Domain (X := X) Q))))
    (b : Q) (hb : orderOf b = 4)
    (y : Normalizer Q) (hy : orderOf y.val = 2)
    (hcomm : ∀ q : Q, Commute q.val y.val)
    (hlocal : (fixedBy X y.val ∩ fixedPoints Q X).ncard = 3)
    (hypos : ∃ t : X, t ∉ fixedPoints Q X ∧ y.val • t = t) :
    (fixedBy X y.val \ fixedPoints Q X).ncard = 4 ∧
      (fixedBy X (b.val ^ 2 * y.val) \ fixedPoints Q X).ncard = 4 ∧
      (fixedBy X (b.val * y.val) \ fixedPoints Q X).ncard = 0 ∧
      (fixedBy X (b.val⁻¹ * y.val) \ fixedPoints Q X).ncard = 0 ∧
      Disjoint (fixedBy X y.val \ fixedPoints Q X)
        (fixedBy X (b.val ^ 2 * y.val) \ fixedPoints Q X) ∧
      Nat.card (Function.fixedPoints (NormalizerSevenOrbitCount.orbitPerm (X := X) Q y)) = 2 := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let bI : Inside Q := ⟨⟨b.val, Q.le_normalizer b.property⟩, b.property⟩
  have hI : Nat.card (Inside Q) = 4 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe Q.le_normalizer).toEquiv).trans hQ
  let eQ : Inside Q ≃* Q := Subgroup.subgroupOfEquivOfLe Q.le_normalizer
  have hbI : orderOf bI = 4 :=
    (orderOf_injective eQ.toMonoidHom eQ.injective bI).symm.trans hb
  have hbG : orderOf b.val = 4 := (Subgroup.orderOf_coe b).trans hb
  have hb4 : b.val ^ 4 = 1 := hbG ▸ pow_orderOf_eq_one b.val
  have hy2 : y.val ^ 2 = 1 := hy ▸ pow_orderOf_eq_one y.val
  have ha2 : (b.val ^ 2 * y.val) ^ 2 = 1 := by
    rw [((hcomm b).pow_left 2).mul_pow, ← pow_mul, hy2, mul_one]
    exact hb4
  have halocal : (fixedBy X (b.val ^ 2 * y.val) ∩ fixedPoints Q X).ncard = 3 := by
    rw [TwoGroupCosetFixedBound.coset_fixed_inter Q ⟨b.val ^ 2, Q.pow_mem b.property 2⟩ y.val]
    exact hlocal
  have hane : b.val ^ 2 * y.val ≠ 1 := by
    intro he
    rw [he, fixedBy_one_eq_univ, Set.univ_inter] at halocal
    have hs : (fixedPoints Q X).ncard = 7 := by simpa only [Nat.card_coe_set_eq] using hseven
    omega
  have haorder : orderOf (b.val ^ 2 * y.val) = 2 := orderOf_eq_prime ha2 hane
  have hyn : y ^ 2 = 1 := Subtype.ext hy2
  have hcent (q : Inside Q) : Commute q.val y :=
    Subtype.ext (hcomm (⟨q.val.val, q.property⟩ : Q)).eq
  have hypos' : ∃ t : Domain (X := X) Q, y • t = t := by
    obtain ⟨t, ht, hyt⟩ := hypos
    exact ⟨⟨t, ht⟩, Subtype.ext hyt⟩
  have hybound : Nat.card (fixedBy (Domain (X := X) Q) y) ≤ 4 := by
    rw [fixed_card]
    exact outside_le_four hmax Q y.val hy hlocal
  have habound : Nat.card (fixedBy (Domain (X := X) Q) (bI.val ^ 2 * y)) ≤ 4 := by
    rw [fixed_card]
    exact outside_le_four hmax Q _ haorder halocal
  obtain ⟨hyfour, hafour, hbzero, hb3zero, hdis, htwo⟩ := CyclicFourFreeCoset.counts
    (Inside Q) hI (free_inside Q hfree) bI hbI (NormalizerSevenOrbitCount.lift Q y)
    hyn hcent heven hypos' hybound habound
  have hbthree : b.val ^ 3 = b.val⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, hb4]
  refine ⟨?_, ?_, ?_, ?_, ?_, htwo⟩
  · rwa [fixed_card] at hyfour
  · rwa [fixed_card] at hafour
  · rwa [fixed_card] at hbzero
  · rw [fixed_card] at hb3zero
    change (fixedBy X (b.val ^ 3 * y.val) \ fixedPoints Q X).ncard = 0 at hb3zero
    rwa [hbthree] at hb3zero
  · rw [Set.disjoint_left] at hdis ⊢
    intro t ht hat
    exact hdis (show (⟨t, ht.2⟩ : Domain (X := X) Q) ∈ fixedBy (Domain (X := X) Q) y from
      Subtype.ext ht.1) (Subtype.ext hat.1)

end FiveTransitive.CyclicFourDoubleSwap

end CFSG
