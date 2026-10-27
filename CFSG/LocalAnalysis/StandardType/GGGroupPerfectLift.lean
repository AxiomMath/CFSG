module

public import Mathlib.Algebra.Group.Commutator
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.GroupTheory.Solvable
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Order.OrderIsoNat

public section

namespace CFSG.StandardType

open scoped commutatorElement

theorem exists_perfect_lift {A B : Type*} [Group A] [Finite A] [Group B] (f : A →* B)
    (hf : Function.Surjective f) {N : Subgroup A}
    (hN : ⁅(⊤ : Subgroup A), (⊤ : Subgroup A)⁆ ≤ N) {Y : Subgroup B} (hY : ⁅Y, Y⁆ = Y) :
    ∃ P : Subgroup A, P ≤ N ∧ ⁅P, P⁆ = P ∧ P.map f = Y := by
  haveI : Finite (Subgroup A) :=
    Finite.of_injective (fun H : Subgroup A => (H : Set A))
      (SetLike.coe_injective : Function.Injective (fun H : Subgroup A => (H : Set A)))
  let D : ℕ → Subgroup A := fun k => Nat.rec (Y.comap f) (fun _ H => ⁅H, H⁆) k
  have hD0 : D 0 = Y.comap f := rfl
  have hDsucc : ∀ k, D (k + 1) = ⁅D k, D k⁆ := fun k => rfl
  have hanti : Antitone D := by
    apply antitone_nat_of_succ_le
    intro k
    rw [hDsucc k]
    exact Subgroup.commutator_le_self (D k)
  obtain ⟨k, hk⟩ := WellFoundedLT.antitone_chain_condition hanti
  have hstab : D (k + 1) = D k := (hk (k + 1) (Nat.le_succ k)).symm
  have hmap : ∀ j, (D j).map f = Y := by
    intro j
    induction j with
    | zero => rw [hD0, Subgroup.map_comap_eq_self_of_surjective hf Y]
    | succ j ih => rw [hDsucc j, Subgroup.map_commutator, ih, hY]
  have hle : ∀ j, D (j + 1) ≤ N := by
    intro j
    rw [hDsucc j]
    exact (Subgroup.commutator_mono le_top le_top).trans hN
  exact ⟨D k, hstab ▸ hle k, (hDsucc k).trans hstab, hmap k⟩

end CFSG.StandardType
