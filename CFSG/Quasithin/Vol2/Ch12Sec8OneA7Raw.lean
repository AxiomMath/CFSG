module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.ZMod.Defs

public section

namespace CFSG.Quasithin.H13

namespace A7Mod

@[expose] def rr : Equiv.Perm (Fin 7) := Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3

@[expose] def tt : Equiv.Perm (Fin 7) := Equiv.swap 0 2

@[expose] def kk : Equiv.Perm (Fin 7) := Equiv.swap 4 5

@[expose] def S0list : List (Equiv.Perm (Fin 7)) :=
  (List.range 4).flatMap fun a => (List.range 2).flatMap fun b =>
    (List.range 2).map fun c => rr ^ a * tt ^ b * kk ^ c

@[expose] def y1 : Equiv.Perm (Fin 7) := Equiv.swap 0 1 * Equiv.swap 1 2

@[expose] def y2 : Equiv.Perm (Fin 7) := Equiv.swap 4 5 * Equiv.swap 5 6

@[expose] def Ylist : List (Equiv.Perm (Fin 7)) :=
  (List.range 3).flatMap fun i => (List.range 3).map fun j => y1 ^ i * y2 ^ j

@[expose] def w1 : Fin 7 → ZMod 2 := ![1, 1, 1, 1, 0, 0, 0]

@[expose] def w2 : Fin 7 → ZMod 2 := ![0, 0, 0, 0, 1, 1, 0]

@[expose] def w3 : Fin 7 → ZMod 2 := ![1, 1, 1, 1, 1, 1, 0]

@[expose] def J1 : Finset (Fin 7) := {0, 1, 2, 3}

@[expose] def J2 : Finset (Fin 7) := {4, 5}

@[expose] def J3 : Finset (Fin 7) := {4, 5, 6}

@[expose] def cenList (J : Finset (Fin 7)) : List (Equiv.Perm (Fin 7)) :=
  S0list.filter fun s => decide (∀ u : Fin 7 → ZMod 2, ∑ i, u i = 0 → (∀ i ∈ J, u i = 0) →
    ∀ i, u (s⁻¹ i) = u i)

@[expose] def UFacts (w : Fin 7 → ZMod 2) (J : Finset (Fin 7)) : Prop :=
  (∀ s ∈ S0list, ∀ i ∈ J, s⁻¹ i ∈ J) ∧
    (∀ u : Fin 7 → ZMod 2, ∑ i, u i = 0 → (∀ i ∈ J, u i = 0) → ∑ i, w i * u i = 0) ∧
    ∃ i ∈ J, w i ≠ 0

@[expose] def A7Raw : Prop :=
  (∀ v : Fin 7 → ZMod 2, ∑ i, v i = 0 →
    ((Finset.univ.filter fun σ : Equiv.Perm (Fin 7) =>
        Equiv.Perm.sign σ = 1 ∧ ∀ i, v (σ⁻¹ i) = v i).card = 360 ↔
      ∃ p : Fin 7, ∀ i, v i = if i = p then 0 else 1)) ∧
  (1 ∈ S0list ∧ (∀ a ∈ S0list, ∀ b ∈ S0list, a * b ∈ S0list) ∧
    (∀ a ∈ S0list, a⁻¹ ∈ S0list) ∧ S0list.Nodup ∧ S0list.length = 16 ∧
    (S0list.filter fun s => decide (Equiv.Perm.sign s = 1)).length = 8) ∧
  (∀ v : Fin 7 → ZMod 2, ∑ i, v i = 0 →
    (∀ s ∈ S0list, Equiv.Perm.sign s = 1 → ∀ i, v (s⁻¹ i) = v i) →
      v = 0 ∨ v = w1 ∨ v = w2 ∨ v = w3) ∧
  UFacts w1 J1 ∧ UFacts w2 J2 ∧ UFacts w3 J3 ∧
    (cenList J2).length ≤ 2 ∧ (cenList J3).length ≤ 2 ∧ (cenList J1).length ≤ 8 ∧
    (∃ a ∈ cenList J1, ∃ b ∈ cenList J1, a * b ≠ b * a) ∧
  (1 ∈ Ylist ∧ (∀ a ∈ Ylist, ∀ b ∈ Ylist, a * b ∈ Ylist) ∧ (∀ a ∈ Ylist, a⁻¹ ∈ Ylist) ∧
    Ylist.Nodup ∧ Ylist.length = 9 ∧ (∀ a ∈ Ylist, ∀ b ∈ Ylist, a * b = b * a) ∧
    ∀ a ∈ Ylist, a ^ 3 = 1 ∧ Equiv.Perm.sign a = 1 ∧ ∀ i, w1 (a⁻¹ i) = w1 i)

end A7Mod

end CFSG.Quasithin.H13
