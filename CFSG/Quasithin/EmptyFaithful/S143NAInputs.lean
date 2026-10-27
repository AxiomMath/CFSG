module

public import CFSG.Quasithin.EmptyFaithful.S143LA
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.NumberTheory.ArithmeticFunction.Misc

public section

namespace CFSG.Quasithin.S143

namespace A6Model

@[expose] def unitVec (p : Fin 6) : Fin 6 → ZMod 2 := fun i => if i = p then 1 else 0

@[expose] def OddCases (Vl : List (Equiv.Perm (Fin 6))) (s : Equiv.Perm (Fin 6)) : Prop :=
  ∀ w : Fin 6 → ZMod 2, VanL Vl w → ¬ wEven w →
    ∃ p : Fin 6, s p ≠ p ∧ ∀ σ : Equiv.Perm (Fin 6), σ.sign = 1 → rawD w σ = rawD (unitVec p) σ

@[expose] def Vr1 : List (Equiv.Perm (Fin 6)) :=
  [Equiv.swap 0 1 * Equiv.swap 3 4, Equiv.swap 0 1 * Equiv.swap 2 5, Equiv.swap 2 5 * Equiv.swap 3 4]

@[expose] def Vr2 : List (Equiv.Perm (Fin 6)) :=
  [Equiv.swap 0 4 * Equiv.swap 3 5, Equiv.swap 1 2 * Equiv.swap 3 5, Equiv.swap 0 4 * Equiv.swap 1 2]

end A6Model

end CFSG.Quasithin.S143
