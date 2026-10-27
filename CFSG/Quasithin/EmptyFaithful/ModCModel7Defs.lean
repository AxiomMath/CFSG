module

public import CFSG.Quasithin.EmptyFaithful.ModCBase

public section

namespace CFSG.Quasithin.ModC

open Equiv Equiv.Perm CFSG.Quasithin.G6

namespace M7

set_option maxRecDepth 100000

@[expose] def a : PermMod 7 := ev 7 [0, 1, 2, 3]
@[expose] def b : PermMod 7 := ev 7 [4, 5]
@[expose] def w : PermMod 7 := ev 7 [0, 1, 4, 5]
@[expose] def x : PermMod 7 := a * b
@[expose] def t1 : PermMod 7 := ev 7 [4, 6]
@[expose] def t2 : PermMod 7 := ev 7 [5, 6]

@[expose] def gens : List (Perm (Fin 7)) := [swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 1 * swap 4 5]

@[expose] def D0 : Subgroup (Perm (Fin 7)) := Subgroup.closure {s | s ∈ gens}

@[expose] def elts : List (Perm (Fin 7)) :=
  [1, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, (swap 0 1 * swap 2 3) * (swap 0 2 * swap 1 3),
   swap 0 1 * swap 4 5, (swap 0 1 * swap 2 3) * (swap 0 1 * swap 4 5),
   (swap 0 2 * swap 1 3) * (swap 0 1 * swap 4 5),
   ((swap 0 1 * swap 2 3) * (swap 0 2 * swap 1 3)) * (swap 0 1 * swap 4 5)]

@[expose] def CondZ (z : PermMod 7) : Prop :=
  (∑ i, Multiplicative.toAdd z i = 0) ∧ z ≠ 1 ∧ (∀ s ∈ gens, permAct 7 s z = z)

instance (z : PermMod 7) : Decidable (CondZ z) := by unfold CondZ; infer_instance

@[expose] def CondV (z v : PermMod 7) : Prop :=
  (∑ i, Multiplicative.toAdd v i = 0) ∧ v ≠ 1 ∧ v ≠ z ∧
    (∀ s ∈ gens, permAct 7 s v = v ∨ permAct 7 s v = z * v) ∧
    (wt v = wt z ∨ wt (z * v) = wt z)

instance (z v : PermMod 7) : Decidable (CondV z v) := by unfold CondV; infer_instance

@[expose] def Concl (z v : PermMod 7) : Prop := (z = a ∧ (v = w ∨ v = a * w)) ∨ (z = b ∧ (v = t1 ∨ v = t2))

instance (z v : PermMod 7) : Decidable (Concl z v) := by unfold Concl; infer_instance

@[expose] def GTri (g : Perm (Fin 7)) : Prop :=
  permAct 7 g b = b ∧ g ^ 3 = 1 ∧ ∃ v ∈ [t1, t2], permAct 7 g v ≠ v ∧ permAct 7 g v ≠ b * v

instance (g : Perm (Fin 7)) : Decidable (GTri g) := by unfold GTri; infer_instance

@[expose] def stab45 : Subgroup (Perm (Fin 7)) where
  carrier := {σ | ∀ i : Fin 7, (σ i = 4 ∨ σ i = 5) ↔ (i = 4 ∨ i = 5)}
  mul_mem' := fun {σ τ} hσ hτ i => by
    show ((σ * τ) i = 4 ∨ (σ * τ) i = 5) ↔ _
    rw [Perm.mul_apply]
    exact (hσ (τ i)).trans (hτ i)
  one_mem' := fun i => Iff.rfl
  inv_mem' := fun {σ} hσ i => by
    show (σ⁻¹ i = 4 ∨ σ⁻¹ i = 5) ↔ _
    have := hσ (σ⁻¹ i)
    have e : σ (σ⁻¹ i) = i := by simp
    rw [e] at this
    exact this.symm

instance : DecidablePred (· ∈ stab45) := fun σ => by
  show Decidable (∀ i : Fin 7, (σ i = 4 ∨ σ i = 5) ↔ (i = 4 ∨ i = 5))
  infer_instance

end M7

end CFSG.Quasithin.ModC
