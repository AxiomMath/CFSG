module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.Quasithin.RonanE628

@[expose] def a5GoodAt (p : Fin 5) (w : Fin 5 → ZMod 2) : Prop :=
  ∃ σ : Equiv.Perm (Fin 5), σ ^ 3 = 1 ∧ σ ≠ 1 ∧ σ p ≠ p ∧ (fun i => w (σ i)) = w

@[expose] def a5BadAt (p : Fin 5) (w : Fin 5 → ZMod 2) : Prop :=
  (∃ i : Fin 5, i ≠ p ∧ w = fun j => if j = i ∨ j = p then 1 else 0) ∨
    w = fun j => if j = p then 0 else 1

instance (p : Fin 5) (w : Fin 5 → ZMod 2) : Decidable (a5GoodAt p w) :=
  inferInstanceAs (Decidable (∃ σ : Equiv.Perm (Fin 5), σ ^ 3 = 1 ∧ σ ≠ 1 ∧ σ p ≠ p ∧
    (fun i => w (σ i)) = w))

instance (p : Fin 5) (w : Fin 5 → ZMod 2) : Decidable (a5BadAt p w) :=
  inferInstanceAs (Decidable ((∃ i : Fin 5, i ≠ p ∧ w = fun j => if j = i ∨ j = p then 1 else 0) ∨
    w = fun j => if j = p then 0 else 1))

theorem a5_good_or_bad : ∀ (p : Fin 5) (w : Fin 5 → ZMod 2), ∑ i, w i = 0 →
    a5GoodAt p w ∨ a5BadAt p w := by
  decide +kernel

theorem a5_bad_sum_not_bad : ∀ (p : Fin 5) (a b : Fin 5 → ZMod 2), a ≠ b →
    ¬ (a5BadAt p a ∧ a5BadAt p b ∧ a5BadAt p (a + b)) := by
  decide +kernel

theorem a5Module_good_at (p : Fin 5) (a b : Fin 5 → ZMod 2) (ha : ∑ i, a i = 0) (hb : ∑ i, b i = 0)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab : a ≠ b) :
    ∃ w ∈ ({a, b, a + b} : Set (Fin 5 → ZMod 2)), ∃ σ : Equiv.Perm (Fin 5),
      orderOf σ = 3 ∧ σ p ≠ p ∧ (fun i => w (σ i)) = w := by
  clear ha0 hb0
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have key : ∀ w : Fin 5 → ZMod 2, a5GoodAt p w →
      ∃ σ : Equiv.Perm (Fin 5), orderOf σ = 3 ∧ σ p ≠ p ∧ (fun i => w (σ i)) = w := by
    rintro w ⟨σ, h3, h1, hp, hw⟩
    exact ⟨σ, orderOf_eq_prime h3 h1, hp, hw⟩
  have hsum : ∑ i, (a + b) i = 0 := by
    simp only [Pi.add_apply, Finset.sum_add_distrib, ha, hb, add_zero]
  by_cases hA : a5GoodAt p a
  · exact ⟨a, Set.mem_insert _ _, key a hA⟩
  by_cases hB : a5GoodAt p b
  · exact ⟨b, Set.mem_insert_of_mem _ (Set.mem_insert _ _), key b hB⟩
  by_cases hC : a5GoodAt p (a + b)
  · exact ⟨a + b, Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)),
      key (a + b) hC⟩
  have hA' := (a5_good_or_bad p a ha).resolve_left hA
  have hB' := (a5_good_or_bad p b hb).resolve_left hB
  have hC' := (a5_good_or_bad p (a + b) hsum).resolve_left hC
  exact (a5_bad_sum_not_bad p a b hab ⟨hA', hB', hC'⟩).elim

end CFSG.Quasithin.RonanE628
