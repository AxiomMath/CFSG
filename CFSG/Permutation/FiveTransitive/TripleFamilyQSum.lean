module

public import CFSG.Permutation.FiveTransitive.TripleFamilySumCore

public section

namespace CFSG

namespace FiveTransitive.TripleFamilyQSum
open Equiv TripleFamilySumCore
open scoped BigOperators

private theorem qCount_eq_filter {X : Type*} [Fintype X] [DecidableEq X] (g v : Perm X) :
    qCount g v = (g.support.filter fun x => v x ≠ x ∧ v (g x) ≠ g x).card := by
  unfold qCount
  congr 1
  ext x
  simp only [intersection, Finset.mem_filter, Finset.mem_inter, Perm.mem_support]
  constructor
  · rintro ⟨⟨hg, hv⟩, _, hvg⟩
    exact ⟨hg, hv, hvg⟩
  · rintro ⟨hg, hv, hvg⟩
    exact ⟨⟨hg, hv⟩, fun h => hg (g.injective h), hvg⟩

theorem sum_qCount
    {T X : Type*} [Fintype T] [Fintype X] [DecidableEq X]
    (g : Perm X) (S : Finset X) (c : X) (hc : c ∈ S)
    (v : T → Perm X) (hmove : ∀ t, v t c ≠ c)
    (hfix : ∀ t x, x ∈ S → x ≠ c → v t x = x)
    (hpoint : ∀ x, x ∉ S → Nat.card {t : T // v t x ≠ x} * (Fintype.card X - 3) =
      Nat.card T * (g.support.card - 1))
    (hboth : ∀ x y, x ∉ S → y ∉ S → x ≠ y →
      Nat.card {t : T // v t x ≠ x ∧ v t y ≠ y} * (Fintype.card X - 3) * (Fintype.card X - 4) =
        Nat.card T * (g.support.card - 1) * (g.support.card - 2)) :
    (∑ t : T, qCount g (v t)) * ((Fintype.card X - 3) * (Fintype.card X - 4)) =
      Nat.card T * (distinguishedEdges g S c).card * (g.support.card - 1) * (Fintype.card X - 4) +
      Nat.card T * (outerEdges g S).card * (g.support.card - 1) * (g.support.card - 2) := by
  classical
  let a := Nat.card T * (g.support.card - 1) * (Fintype.card X - 4)
  let b := Nat.card T * (g.support.card - 1) * (g.support.card - 2)
  let D := (Fintype.card X - 3) * (Fintype.card X - 4)
  have hf (x : X) (hx : x ∈ g.support) :
      Nat.card {t : T // v t x ≠ x ∧ v t (g x) ≠ g x} * D =
        (if (x = c ∧ g x ∉ S) ∨ (x ∉ S ∧ g x = c) then a else 0) +
        (if x ∉ S ∧ g x ∉ S then b else 0) := by
    have hg : g x ≠ x := Perm.mem_support.mp hx
    have hz₁ (hxS : x ∈ S) (hxc : x ≠ c) :
        Nat.card {t : T // v t x ≠ x ∧ v t (g x) ≠ g x} = 0 := by
      apply Nat.card_eq_zero.mpr
      exact Or.inl ⟨fun t => t.property.1 (hfix t.val x hxS hxc)⟩
    have hz₂ (hgS : g x ∈ S) (hgc : g x ≠ c) :
        Nat.card {t : T // v t x ≠ x ∧ v t (g x) ≠ g x} = 0 := by
      apply Nat.card_eq_zero.mpr
      exact Or.inl ⟨fun t => t.property.2 (hfix t.val (g x) hgS hgc)⟩
    by_cases hxS : x ∈ S
    · by_cases hxc : x = c
      · subst x
        by_cases hgS : g c ∈ S
        · simp only [hz₂ hgS hg, zero_mul, hgS, not_true_eq_false, hc, true_and,
            false_and, or_self, if_false, add_zero]
        · have heq : Nat.card {t : T // v t c ≠ c ∧ v t (g c) ≠ g c} =
              Nat.card {t : T // v t (g c) ≠ g c} :=
            card_pred_congr _ _ (fun t => ⟨fun h => h.2, fun h => ⟨hmove t, h⟩⟩)
          rw [heq]
          simp only [hgS, not_false_eq_true, hc, not_true_eq_false, and_true,
            false_and, or_false, if_true, if_false, add_zero]
          exact (by simpa only [D, a, mul_assoc] using congrArg (fun z : ℕ => z * (Fintype.card X - 4)) (hpoint (g c) hgS))
      · simp only [hz₁ hxS hxc, zero_mul, hxc, false_and, hxS, not_true_eq_false,
          or_self, if_false, add_zero]
    · by_cases hgS : g x ∈ S
      · by_cases hgc : g x = c
        · have heq : Nat.card {t : T // v t x ≠ x ∧ v t (g x) ≠ g x} =
              Nat.card {t : T // v t x ≠ x} :=
            card_pred_congr _ _ (fun t => ⟨fun h => h.1, fun h => ⟨h, by rw [hgc]; exact hmove t⟩⟩)
          rw [heq]
          have hxc : x ≠ c := fun he => hxS (he ▸ hc)
          simp only [hxc, hxS, not_false_eq_true, hgc, hc, not_true_eq_false,
            and_false, and_true, or_true, if_true, if_false, add_zero]
          exact (by simpa only [D, a, mul_assoc] using congrArg (fun z : ℕ => z * (Fintype.card X - 4)) (hpoint x hxS))
        · simp only [hz₂ hgS hgc, zero_mul, hgS, not_true_eq_false, and_false,
            hgc, or_self, if_false, add_zero]
      · have hxc : x ≠ c := fun he => hxS (he ▸ hc)
        have hgc : g x ≠ c := fun he => hgS (he ▸ hc)
        simp only [hxc, false_and, hgc, and_false, or_self, if_false, hxS, hgS,
          not_false_eq_true, and_self, if_true, zero_add]
        simpa only [D, b, mul_assoc] using hboth x (g x) hxS hgS hg.symm
  simp only [qCount_eq_filter]
  rw [FamilyCommutatorAverage.sum_card_filter, Finset.sum_mul]
  change (∑ x ∈ g.support, Nat.card {t : T // v t x ≠ x ∧ v t (g x) ≠ g x} * D) = _
  rw [Finset.sum_congr rfl hf, Finset.sum_add_distrib]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  simp only [Finset.sum_const, smul_eq_mul]
  change (distinguishedEdges g S c).card * a + (outerEdges g S).card * b = _
  dsimp only [a, b]
  ac_rfl

end FiveTransitive.TripleFamilyQSum

end CFSG
