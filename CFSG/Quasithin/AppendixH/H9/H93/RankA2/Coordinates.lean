module

public import CFSG.Quasithin.AppendixH.H9.H93.ExplicitDefs
public import CFSG.Quasithin.AppendixH.H9.ModelBasic

public section

namespace CFSG.ASVolI.ChH

namespace A2Coords

@[expose] def A2Fixed (x : Fin 4 → ZMod 2) : Prop := x 0 = x 1 ∧ x 2 = x 3

instance : DecidablePred A2Fixed := fun x => inferInstanceAs (Decidable (x 0 = x 1 ∧ x 2 = x 3))

@[expose] def A2Fixes (ε a b : Fin 4 → ZMod 2) : Prop := A2fst ε a b = a ∧ A2snd ε a b = b

instance (ε a b : Fin 4 → ZMod 2) : Decidable (A2Fixes ε a b) :=
  inferInstanceAs (Decidable (A2fst ε a b = a ∧ A2snd ε a b = b))

theorem A2vec_zero : ∀ ε : Fin 4 → ZMod 2, A2vec ε 0 = 0 := by decide

theorem A2vec_of_A2Fixed : ∀ ε x : Fin 4 → ZMod 2, A2Fixed x → A2vec ε x = x := by decide

theorem A2Fixed_zero : A2Fixed 0 := by decide

theorem A2_add_self : ∀ a : Fin 4 → ZMod 2, a + a = 0 := by decide

theorem A2_eps3_eq_one_of_ne_zero : ∀ ε : Fin 4 → ZMod 2, ε 3 ≠ 0 → ε 3 = 1 := by decide

theorem A2fst_of_eps3_eq_one : ∀ ε : Fin 4 → ZMod 2, ε 3 = 1 → ∀ a b : Fin 4 → ZMod 2,
    A2fst ε a b = A2vec ε b := by decide

theorem A2snd_of_eps3_eq_one : ∀ ε : Fin 4 → ZMod 2, ε 3 = 1 → ∀ a b : Fin 4 → ZMod 2,
    A2snd ε a b = A2vec ε a := by decide

theorem forall_A2Fixes_of_eps3_eq_zero_iff : ∀ a b : Fin 4 → ZMod 2,
    (∀ ε : Fin 4 → ZMod 2, ε 3 = 0 → A2Fixes ε a b) ↔ A2Fixed a ∧ A2Fixed b := by decide

theorem forall_A2Fixes_iff : ∀ a b : Fin 4 → ZMod 2,
    (∀ ε : Fin 4 → ZMod 2, A2Fixes ε a b) ↔ A2Fixed a ∧ a = b := by decide

theorem A2Fixes_iff_of_eps3_eq_one : ∀ ε : Fin 4 → ZMod 2, ε 3 = 1 → ∀ a b : Fin 4 → ZMod 2,
    A2Fixes ε a b ↔ A2vec ε b = a := by decide

theorem A2vec_add : ∀ ε u v : Fin 4 → ZMod 2, A2vec ε (u + v) = A2vec ε u + A2vec ε v := by
  decide

theorem A2Fixed_add : ∀ x y : Fin 4 → ZMod 2, A2Fixed x → A2Fixed y → A2Fixed (x + y) := by
  decide

theorem A2Fixed_add_A2vec_add {x y : Fin 4 → ZMod 2} (hx : A2Fixed x) (hy : A2Fixed y)
    (y' ε : Fin 4 → ZMod 2) : A2Fixed ((x + A2vec ε y') + A2vec ε (y + y')) := by
  rw [A2vec_add, A2vec_of_A2Fixed ε y hy, add_add_add_comm, A2_add_self, add_zero]
  exact A2Fixed_add x y hx hy

theorem A2Fixed_of_four_le_card : ∀ X Y : Fin 4 → ZMod 2,
    4 ≤ Fintype.card {δ : Fin 4 → ZMod 2 // A2Fixes δ X Y} →
      ∀ ε : Fin 4 → ZMod 2, ε 3 = 1 → A2Fixed (X + A2vec ε Y) := by decide

theorem four_le_card_A2Fixes_of_A2Fixed : ∀ X Y : Fin 4 → ZMod 2, A2Fixed X → A2Fixed Y →
    4 ≤ Fintype.card {δ : Fin 4 → ZMod 2 // A2Fixes δ X Y} := by decide

theorem four_le_card_A2Fixes_A2vec : ∀ ε : Fin 4 → ZMod 2, ε 3 = 1 → ∀ Y : Fin 4 → ZMod 2,
    4 ≤ Fintype.card {δ : Fin 4 → ZMod 2 // A2Fixes δ (A2vec ε Y) Y} := by decide

theorem card_A2_diagonal :
    Fintype.card {p : (Fin 4 → ZMod 2) × (Fin 4 → ZMod 2) // A2Fixed p.1 ∧ p.1 = p.2} = 4 := by
  decide

theorem card_A2_radical : ∀ ε : Fin 4 → ZMod 2, ε 3 = 1 →
    Fintype.card {p : (Fin 4 → ZMod 2) × (Fin 4 → ZMod 2) // A2Fixed (p.1 + A2vec ε p.2)} = 64 := by
  decide

theorem card_eq_fintype_card_of_pairVec_mem_iff (S : Subgroup (PairN 4))
    (P : (Fin 4 → ZMod 2) × (Fin 4 → ZMod 2) → Prop) [DecidablePred P]
    (h : ∀ a b : Fin 4 → ZMod 2, pairVec a b ∈ S ↔ P (a, b)) :
    Nat.card S = Fintype.card {p // P p} := by
  rw [← Nat.card_eq_fintype_card]
  refine Nat.card_congr (Equiv.subtypeEquiv
    (Equiv.prodCongr Multiplicative.toAdd Multiplicative.toAdd) ?_)
  intro x
  obtain ⟨a, b, rfl⟩ := pairVec_surj x
  exact h a b

theorem rk_eq_of_card_eq_two_pow {G : Type*} [Group G] (S : Subgroup G) (n : ℕ)
    (h : Nat.card S = 2 ^ n) : CFSG.Quasithin.rk ↥S = n := by
  unfold CFSG.Quasithin.rk
  rw [h]
  exact padicValNat.prime_pow n

end A2Coords

end CFSG.ASVolI.ChH
