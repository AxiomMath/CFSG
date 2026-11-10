module

public import CFSG.Permutation.FiveTransitive.CyclePatternSum
public import Mathlib.Data.Set.Card
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Basic.Finite.Sum

public section

namespace CFSG

namespace FiveTransitive.CyclePatternMixed

open Equiv CyclePatternRoots CyclePatternSum

variable {X : Type*}

abbrev doubleTwo : Perm (Fin 2 ⊕ Fin 2) := (finRotate 2).sumCongr (finRotate 2)
abbrev fourTwo : Perm (Fin 4 ⊕ Fin 2) := (finRotate 4).sumCongr (finRotate 2)
abbrev fourTwoTwo : Perm (Fin 4 ⊕ (Fin 2 ⊕ Fin 2)) := (finRotate 4).sumCongr doubleTwo

private theorem two_period (g : Perm X) (a : Pattern g (finRotate 2)) (i : Fin 2) :
    g (g (a.val i)) = a.val i := by
  rw [a.property, a.property]
  congr 1
  fin_cases i <;> rfl

theorem four_not_two_period (g : Perm X) (a : Pattern g (finRotate 4)) (i : Fin 4) :
    g (g (a.val i)) ≠ a.val i := by
  rw [a.property, a.property]
  apply a.val.injective.ne
  fin_cases i <;> decide

private theorem four_two_disjoint (g : Perm X) (a : Pattern g (finRotate 4))
    (b : Pattern g (finRotate 2)) (i : Fin 4) (j : Fin 2) :
    a.val i ≠ b.val j := by
  intro h
  apply four_not_two_period g a i
  rw [h, two_period g b j]

private theorem two_disjoint_iff (g : Perm X) (a b : Pattern g (finRotate 2)) :
    (∀ i j, a.val i ≠ b.val j) ↔ b.val 0 ≠ a.val 0 ∧ b.val 0 ≠ a.val 1 := by
  have ha0 : g (a.val 0) = a.val 1 := a.property 0
  have ha1 : g (a.val 1) = a.val 0 := a.property 1
  have hb0 : g (b.val 0) = b.val 1 := b.property 0
  have hb1 : g (b.val 1) = b.val 0 := b.property 1
  constructor
  · intro h
    exact ⟨(h 0 0).symm, (h 1 0).symm⟩
  · rintro ⟨h0,h1⟩ i j
    fin_cases i <;> fin_cases j
    · exact h0.symm
    · intro h
      change a.val 0 = b.val 1 at h
      exact h1 (by simpa only [ha0,hb1] using (congrArg g h).symm)
    · exact h1.symm
    · intro h
      change a.val 1 = b.val 1 at h
      exact h0 (by simpa only [ha1,hb1] using (congrArg g h).symm)

private theorem card_two_disjoint [Finite X] (g : Perm X) (a : Pattern g (finRotate 2)) :
    Nat.card {b : Pattern g (finRotate 2) // ∀ i j, a.val i ≠ b.val j} =
      Nat.card (TwoRoot g) - 2 := by
  classical
  have ha0 : g (a.val 0) = a.val 1 := a.property 0
  have ha1 : g (a.val 1) = a.val 0 := a.property 1
  let x0 : TwoRoot g := (twoEquiv g) a
  let x1 : TwoRoot g := ⟨a.val 1, by
    refine ⟨by rw [ha1,ha0], ?_⟩
    rw [ha1]
    exact a.val.injective.ne (by decide)⟩
  have hne : x0 ≠ x1 := by
    intro h
    exact a.val.injective.ne (by decide : (0 : Fin 2) ≠ 1) (congrArg Subtype.val h)
  let E : {b : Pattern g (finRotate 2) // ∀ i j, a.val i ≠ b.val j} ≃
      {y : TwoRoot g // y.val ≠ a.val 0 ∧ y.val ≠ a.val 1} :=
    Equiv.subtypeEquiv (twoEquiv g) (fun b => two_disjoint_iff g a b)
  have hcard := Nat.card_congr E
  change Nat.card {b : Pattern g (finRotate 2) // ∀ i j, a.val i ≠ b.val j} =
    Nat.card {y : TwoRoot g // y.val ≠ a.val 0 ∧ y.val ≠ a.val 1} at hcard
  rw [hcard]
  have heq : {y : TwoRoot g | y.val ≠ a.val 0 ∧ y.val ≠ a.val 1} =
      ({x0,x1} : Set (TwoRoot g))ᶜ := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff, not_or]
    constructor
    · rintro ⟨h0,h1⟩
      exact ⟨fun h => h0 (congrArg Subtype.val h), fun h => h1 (congrArg Subtype.val h)⟩
    · rintro ⟨h0,h1⟩
      exact ⟨fun h => h0 (Subtype.ext h), fun h => h1 (Subtype.ext h)⟩
  change Nat.card ↥({y : TwoRoot g | y.val ≠ a.val 0 ∧ y.val ≠ a.val 1} : Set (TwoRoot g)) = _
  rw [Nat.card_coe_set_eq, heq, Set.ncard_compl]
  simp [hne]

theorem card_double_two [Finite X] (g : Perm X) :
    Nat.card (Pattern g doubleTwo) = Nat.card (TwoRoot g) * (Nat.card (TwoRoot g) - 2) := by
  classical
  let _ : Fintype X := Fintype.ofFinite X
  rw [Nat.card_congr (sumEquiv g (finRotate 2) (finRotate 2))]
  simp only [Nat.card_eq_fintype_card, Fintype.card_sigma]
  have hc (a : Pattern g (finRotate 2)) := card_two_disjoint g a
  simp only [Nat.card_eq_fintype_card] at hc
  simp_rw [hc]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have ht := card_two_pattern g
  simp only [Nat.card_eq_fintype_card] at ht
  rw [ht]

theorem card_four_two [Finite X] (g : Perm X) :
    Nat.card (Pattern g fourTwo) = Nat.card (FourRoot g) * Nat.card (TwoRoot g) := by
  rw [card_sum_of_disjoint g (finRotate 4) (finRotate 2) (four_two_disjoint g),
    card_four_pattern, card_two_pattern]

theorem card_four_two_two [Finite X] (g : Perm X) :
    Nat.card (Pattern g fourTwoTwo) =
      Nat.card (FourRoot g) * Nat.card (TwoRoot g) * (Nat.card (TwoRoot g) - 2) := by
  have hdis (a : Pattern g (finRotate 4)) (b : Pattern g doubleTwo) (i : Fin 4)
      (j : Fin 2 ⊕ Fin 2) : a.val i ≠ b.val j := by
    let b1 : Pattern g (finRotate 2) := ⟨⟨fun j => b.val (Sum.inl j),
      fun _ _ h => Sum.inl_injective (b.val.injective h)⟩, fun j => b.property (Sum.inl j)⟩
    let b2 : Pattern g (finRotate 2) := ⟨⟨fun j => b.val (Sum.inr j),
      fun _ _ h => Sum.inr_injective (b.val.injective h)⟩, fun j => b.property (Sum.inr j)⟩
    cases j with
    | inl j => exact four_two_disjoint g a b1 i j
    | inr j => exact four_two_disjoint g a b2 i j
  rw [card_sum_of_disjoint g (finRotate 4) doubleTwo hdis, card_four_pattern, card_double_two,
    Nat.mul_assoc]

end FiveTransitive.CyclePatternMixed

end CFSG
