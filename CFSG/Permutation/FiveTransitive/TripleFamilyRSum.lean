module

public import CFSG.Permutation.FiveTransitive.TripleFamilySumCore

public section

namespace CFSG

namespace FiveTransitive.TripleFamilyRSum
open Equiv TripleFamilySumCore
open scoped BigOperators

private theorem rCount_eq_edges {X : Type*} [Fintype X] [DecidableEq X] (g v : Perm X) :
    rCount g v = (g.support.offDiag.filter fun p => v p.1 = p.2).card := by
  unfold rCount
  apply Finset.card_bij (fun x _ => (x, v x))
  · intro x hx
    obtain ⟨hx, hvx⟩ := Finset.mem_filter.mp hx
    obtain ⟨hxA, hxv⟩ := Finset.mem_inter.mp hx
    obtain ⟨hvxA, _⟩ := Finset.mem_inter.mp hvx
    exact Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨hxA, hvxA, (Perm.mem_support.mp hxv).symm⟩, rfl⟩
  · intro x _ y _ h
    exact congrArg Prod.fst h
  · intro p hp
    obtain ⟨hp, hv⟩ := Finset.mem_filter.mp hp
    obtain ⟨hxA, hyA, hxy⟩ := Finset.mem_offDiag.mp hp
    have hxv : p.1 ∈ v.support := Perm.mem_support.mpr (fun h => hxy (h.symm.trans hv))
    refine ⟨p.1, Finset.mem_filter.mpr ⟨Finset.mem_inter.mpr ⟨hxA, hxv⟩,
      Finset.mem_inter.mpr ⟨hv ▸ hyA, Perm.apply_mem_support.mpr hxv⟩⟩, ?_⟩
    exact Prod.ext rfl hv

private theorem card_cross_pairs {X : Type*} [DecidableEq X]
    (A S : Finset X) (c : X) (hcA : c ∈ A) (hcS : c ∈ S) :
    (A.offDiag.filter fun p => (p.1 = c ∧ p.2 ∉ S) ∨ (p.1 ∉ S ∧ p.2 = c)).card =
      2 * (A \ S).card := by
  let O := A \ S
  have hcO : c ∉ O := by simp [O, hcS]
  have hset : (A.offDiag.filter fun p => (p.1 = c ∧ p.2 ∉ S) ∨ (p.1 ∉ S ∧ p.2 = c)) =
      O.image (fun x => (c, x)) ∪ O.image (fun x => (x, c)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro ⟨⟨hxA, hyA, _⟩, (⟨hxc, hyS⟩ | ⟨hxS, hyc⟩)⟩
      · exact Or.inl ⟨p.2, Finset.mem_sdiff.mpr ⟨hyA, hyS⟩, Prod.ext hxc.symm rfl⟩
      · exact Or.inr ⟨p.1, Finset.mem_sdiff.mpr ⟨hxA, hxS⟩, Prod.ext rfl hyc.symm⟩
    · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
      · have hx' := Finset.mem_sdiff.mp hx
        exact ⟨⟨hcA, hx'.1, fun he => hcO (by simpa only [← (show c = x from he)] using hx)⟩, Or.inl ⟨rfl, hx'.2⟩⟩
      · have hx' := Finset.mem_sdiff.mp hx
        exact ⟨⟨hx'.1, hcA, fun he => hcO (by simpa only [(show x = c from he)] using hx)⟩, Or.inr ⟨hx'.2, rfl⟩⟩
  have hdis : Disjoint (O.image (fun x => (c, x))) (O.image (fun x => (x, c))) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    obtain ⟨x, hx, hxq⟩ := Finset.mem_image.mp hp
    obtain ⟨y, hy, hyq⟩ := Finset.mem_image.mp hq
    have he : c = y := congrArg Prod.fst (hxq.trans hyq.symm)
    exact hcO (he ▸ hy)
  rw [hset, Finset.card_union_of_disjoint hdis,
    Finset.card_image_of_injective _ (fun x y h => congrArg Prod.snd h),
    Finset.card_image_of_injective _ (fun x y h => congrArg Prod.fst h)]
  change O.card + O.card = 2 * O.card
  omega

theorem sum_rCount
    {T X : Type*} [Fintype T] [Fintype X] [DecidableEq X]
    (g : Perm X) (S : Finset X) (c : X) (hS : S ⊆ g.support) (hScard : S.card = 3) (hc : c ∈ S)
    (v : T → Perm X) (hfix : ∀ t x, x ∈ S → x ≠ c → v t x = x)
    (hfrom : ∀ x, x ∉ S → Nat.card {t : T // v t c = x} * (Fintype.card X - 3) = Nat.card T)
    (hto : ∀ x, x ∉ S → Nat.card {t : T // v t x = c} * (Fintype.card X - 3) = Nat.card T)
    (hpair : ∀ x y, x ∉ S → y ∉ S → x ≠ y →
      Nat.card {t : T // v t x = y} * (Fintype.card X - 3) * (Fintype.card X - 4) =
        Nat.card T * (g.support.card - 2)) :
    (∑ t : T, rCount g (v t)) * ((Fintype.card X - 3) * (Fintype.card X - 4)) =
      2 * Nat.card T * (g.support.card - 3) * (Fintype.card X - 4) +
      Nat.card T * (g.support.card - 2) * (g.support.card - 3) * (g.support.card - 4) := by
  classical
  let a := Nat.card T * (Fintype.card X - 4)
  let b := Nat.card T * (g.support.card - 2)
  let D := (Fintype.card X - 3) * (Fintype.card X - 4)
  have hf (p : X × X) (hp : p ∈ g.support.offDiag) :
      Nat.card {t : T // v t p.1 = p.2} * D =
        (if (p.1 = c ∧ p.2 ∉ S) ∨ (p.1 ∉ S ∧ p.2 = c) then a else 0) +
        (if p.1 ∉ S ∧ p.2 ∉ S then b else 0) := by
    obtain ⟨hxA, hyA, hxy⟩ := Finset.mem_offDiag.mp hp
    have hz₁ (hxS : p.1 ∈ S) (hxc : p.1 ≠ c) : Nat.card {t : T // v t p.1 = p.2} = 0 := by
      apply Nat.card_eq_zero.mpr
      exact Or.inl ⟨fun t => hxy ((hfix t.val p.1 hxS hxc).symm.trans t.property)⟩
    have hz₂ (hyS : p.2 ∈ S) (hyc : p.2 ≠ c) : Nat.card {t : T // v t p.1 = p.2} = 0 := by
      apply Nat.card_eq_zero.mpr
      exact Or.inl ⟨fun t => hxy ((v t.val).injective (t.property.trans (hfix t.val p.2 hyS hyc).symm))⟩
    by_cases hxS : p.1 ∈ S
    · by_cases hxc : p.1 = c
      · have hyc : p.2 ≠ c := fun he => hxy (hxc.trans he.symm)
        by_cases hyS : p.2 ∈ S
        · simp only [hz₂ hyS hyc, zero_mul, hyS, not_true_eq_false, and_false,
            hxS, false_and, or_self, if_false, add_zero]
        · simp only [hxc, hyS, hc, not_false_eq_true, not_true_eq_false, and_true,
            false_and, or_false, if_true, if_false, add_zero]
          exact (by simpa only [D, a, mul_assoc, hxc] using congrArg (fun z : ℕ => z * (Fintype.card X - 4)) (hfrom p.2 hyS))
      · simp only [hz₁ hxS hxc, zero_mul, hxc, false_and, hxS, not_true_eq_false,
          or_self, if_false, add_zero]
    · by_cases hyS : p.2 ∈ S
      · by_cases hyc : p.2 = c
        · have hxc : p.1 ≠ c := fun he => hxS (he ▸ hc)
          simp only [hxc, hxS, not_false_eq_true, hyc, hc, not_true_eq_false,
            and_false, and_true, or_true, if_true, if_false, add_zero]
          exact (by simpa only [D, a, mul_assoc, hyc] using congrArg (fun z : ℕ => z * (Fintype.card X - 4)) (hto p.1 hxS))
        · simp only [hz₂ hyS hyc, zero_mul, hyS, not_true_eq_false, and_false,
            hyc, or_self, if_false, add_zero]
      · have hxc : p.1 ≠ c := fun he => hxS (he ▸ hc)
        have hyc : p.2 ≠ c := fun he => hyS (he ▸ hc)
        simp only [hxc, false_and, hyc, and_false, or_self, if_false, hxS, hyS,
          not_false_eq_true, and_self, if_true, zero_add]
        simpa only [D, b, mul_assoc] using hpair p.1 p.2 hxS hyS hxy
  simp only [rCount_eq_edges]
  rw [FamilyCommutatorAverage.sum_card_filter, Finset.sum_mul]
  change (∑ p ∈ g.support.offDiag, Nat.card {t : T // v t p.1 = p.2} * D) = _
  rw [Finset.sum_congr rfl hf, Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter]
  simp only [Finset.sum_const, smul_eq_mul]
  have hout : (g.support.offDiag.filter fun p => p.1 ∉ S ∧ p.2 ∉ S) = (g.support \ S).offDiag := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_sdiff]
    tauto
  rw [card_cross_pairs g.support S c (hS hc) hc, hout, Finset.offDiag_card,
    Finset.card_sdiff_of_subset hS, hScard]
  have hsub : g.support.card - 3 - 1 = g.support.card - 4 := by omega
  have hpoly : (g.support.card - 3) * (g.support.card - 3) - (g.support.card - 3) =
      (g.support.card - 3) * (g.support.card - 4) := by
    rw [← hsub]
    simpa only [mul_one] using
      (Nat.mul_sub_left_distrib (g.support.card - 3) (g.support.card - 3) 1).symm
  rw [hpoly]
  dsimp only [a, b]
  ac_rfl

end FiveTransitive.TripleFamilyRSum

end CFSG
