module

public import CFSG.Quasithin.AppendixH.H9.H93.ExplicitDefs

public section

namespace CFSG.ASVolI.ChH

open scoped Matrix
open CFSG.Quasithin CFSG.Open

theorem A1fst_snd_single_zero (a b : Fin 4 → ZMod 2) :
    A1fst (Pi.single 0 1) a b = vP01_23 a ∧ A1snd (Pi.single 0 1) a b = vP01_23 b := by
  revert a b
  decide

theorem A1fst_snd_single_one (a b : Fin 4 → ZMod 2) :
    A1fst (Pi.single 1 1) a b = vP02_13 a ∧ A1snd (Pi.single 1 1) a b = vP02_13 b := by
  revert a b
  decide

theorem A1fst_snd_single_two (a b : Fin 4 → ZMod 2) :
    A1fst (Pi.single 2 1) a b = vZJ a ∧ A1snd (Pi.single 2 1) a b = vZJ b := by
  revert a b
  decide

theorem A1fst_snd_single_three (a b : Fin 4 → ZMod 2) :
    A1fst (Pi.single 3 1) a b = b ∧ A1snd (Pi.single 3 1) a b = a := by
  revert a b
  decide

theorem A1_eq_zero_of_fst_snd_eq (ε : Fin 4 → ZMod 2)
    (h : ∀ a b : Fin 4 → ZMod 2, A1fst ε a b = a ∧ A1snd ε a b = b) : ε = 0 := by
  revert ε
  decide

theorem A1vec_single_zero_ne_zero (ε : Fin 4 → ZMod 2) : A1vec ε (Pi.single 0 1) ≠ 0 := by
  revert ε
  decide

theorem A1_vZJ_eq_transvection (a : Fin 4 → ZMod 2) :
    vZJ a = a + ((![1, 1, 1, 1] : Fin 4 → ZMod 2) ⬝ᵥ a) • (![1, 1, 1, 1] : Fin 4 → ZMod 2) := by
  revert a
  decide

theorem A1_vZJ_zero : vZJ 0 = 0 := by decide

theorem A1vec_transvection_cases (ε u f : Fin 4 → ZMod 2)
    (h : ∀ a : Fin 4 → ZMod 2, A1vec ε a = a + (f ⬝ᵥ a) • u) :
    u = 0 ∨ f = 0 ∨ (ε 0 = 0 ∧ ε 1 = 0 ∧ ε 2 = 1) := by
  revert ε u f
  decide

end CFSG.ASVolI.ChH
