module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.GoldschmidtAmalgamSVertex

public section

set_option synthInstance.maxSize 2000

namespace CFSG.Quasithin.F6.GoldAmS

open Matrix

abbrev SL3 := Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)

def K1 : Subgroup SL3 where
  carrier := {g | g.1 1 0 = 0 ∧ g.1 2 0 = 0}
  one_mem' := by decide
  mul_mem' := by
    intro a b ha hb
    revert a b
    decide +kernel
  inv_mem' := by
    intro a ha
    revert a
    decide +kernel

def K2 : Subgroup SL3 where
  carrier := {g | g.1 2 0 = 0 ∧ g.1 2 1 = 0}
  one_mem' := by decide
  mul_mem' := by
    intro a b ha hb
    revert a b
    decide +kernel
  inv_mem' := by
    intro a ha
    revert a
    decide +kernel

def Q1 : Subgroup SL3 where
  carrier := {g | g.1 0 0 = 1 ∧ g.1 1 0 = 0 ∧ g.1 2 0 = 0 ∧ g.1 1 1 = 1 ∧ g.1 1 2 = 0 ∧
    g.1 2 1 = 0 ∧ g.1 2 2 = 1}
  one_mem' := by decide
  mul_mem' := by
    intro a b ha hb
    revert a b
    decide +kernel
  inv_mem' := by
    intro a ha
    revert a
    decide +kernel

def Q2 : Subgroup SL3 where
  carrier := {g | g.1 0 0 = 1 ∧ g.1 0 1 = 0 ∧ g.1 1 0 = 0 ∧ g.1 1 1 = 1 ∧ g.1 2 0 = 0 ∧
    g.1 2 1 = 0 ∧ g.1 2 2 = 1}
  one_mem' := by decide
  mul_mem' := by
    intro a b ha hb
    revert a b
    decide +kernel
  inv_mem' := by
    intro a ha
    revert a
    decide +kernel

instance : DecidablePred (· ∈ K1) := fun g =>
  inferInstanceAs (Decidable (g.1 1 0 = 0 ∧ g.1 2 0 = 0))
instance : DecidablePred (· ∈ K2) := fun g =>
  inferInstanceAs (Decidable (g.1 2 0 = 0 ∧ g.1 2 1 = 0))
instance : DecidablePred (· ∈ Q1) := fun g =>
  inferInstanceAs (Decidable (g.1 0 0 = 1 ∧ g.1 1 0 = 0 ∧ g.1 2 0 = 0 ∧ g.1 1 1 = 1 ∧
    g.1 1 2 = 0 ∧ g.1 2 1 = 0 ∧ g.1 2 2 = 1))
instance : DecidablePred (· ∈ Q2) := fun g =>
  inferInstanceAs (Decidable (g.1 0 0 = 1 ∧ g.1 0 1 = 0 ∧ g.1 1 0 = 0 ∧ g.1 1 1 = 1 ∧
    g.1 2 0 = 0 ∧ g.1 2 1 = 0 ∧ g.1 2 2 = 1))

instance : DecidablePred (· ∈ K1 ⊓ K2) := fun g => inferInstanceAs (Decidable (g ∈ K1 ∧ g ∈ K2))

theorem card_K1 : Nat.card K1 = 24 := by
  rw [Nat.card_eq_fintype_card]; decide +kernel
theorem card_K2 : Nat.card K2 = 24 := by
  rw [Nat.card_eq_fintype_card]; decide +kernel
theorem card_Q1 : Nat.card Q1 = 4 := by
  rw [Nat.card_eq_fintype_card]; decide +kernel
theorem card_Q2 : Nat.card Q2 = 4 := by
  rw [Nat.card_eq_fintype_card]; decide +kernel
theorem card_K12 : Nat.card ↥(K1 ⊓ K2) = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel
theorem card_SL3 : Nat.card SL3 = 168 := by
  rw [Nat.card_eq_fintype_card]; decide +kernel

end CFSG.Quasithin.F6.GoldAmS
