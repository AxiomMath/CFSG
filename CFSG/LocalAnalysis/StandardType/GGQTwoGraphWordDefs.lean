module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Tactic.Bound.Init

public section

namespace CFSG.StandardType

@[expose] def ggQ2gwRefl {n : ℕ} (C : Fin n → Fin n → ZMod 3) (j : Fin n) (x : Fin n → ZMod 3) :
    Fin n → ZMod 3 :=
  fun i => if i = j then x i - ∑ k, C j k * x k else x i

@[expose] def ggQ2gwAct {n : ℕ} (C : Fin n → Fin n → ZMod 3) (l : List (Fin n))
    (x : Fin n → ZMod 3) : Fin n → ZMod 3 :=
  l.foldr (ggQ2gwRefl C) x

@[expose] def ggQ2gwRoot {n : ℕ} (C : Fin n → Fin n → ZMod 3) (j : Fin n) (x : Fin n → ZMod 3) :
    ZMod 3 :=
  ∑ k, C j k * x k

@[expose] def ggQ2gwE {n : ℕ} (k : Fin n) : Fin n → ZMod 3 := fun i => if i = k then 1 else 0

@[expose] def ggQ2gwDot {n : ℕ} (a x : Fin n → ZMod 3) : ZMod 3 := ∑ k, a k * x k

@[expose] def ggQ2gwQ {n : ℕ} (C : Fin n → Fin n → ZMod 3) (wt x : Fin n → ZMod 3) : ZMod 3 :=
  ∑ i, wt i * x i * ggQ2gwRoot C i x

structure GGQ2gwKill where
  d : Fin 4 → ZMod 3
  w : Fin 3 → List (Fin 4)
  j : Fin 3 → Fin 4
  c : Fin 3 → Fin 4 → ZMod 3
  φ : Fin 3 → Fin 4 → ZMod 3
  inv : Fin 4 → Fin 4 → ZMod 3

@[expose] def GGQ2gwKill.OK (C : Fin 4 → Fin 4 → ZMod 3) (E : GGQ2gwKill) : Prop :=
  (∀ m, ggQ2gwAct C (E.w m) (ggQ2gwE (E.j m)) = E.c m) ∧
  (∀ m k, ggQ2gwRoot C (E.j m) (ggQ2gwAct C (E.w m).reverse (ggQ2gwE k)) = E.φ m k) ∧
  (∀ m, ggQ2gwDot (E.φ m) E.d = 0) ∧
  (ggQ2gwDot (E.φ 0) (E.c 1) ≠ 0 ∨ ggQ2gwDot (E.φ 1) (E.c 0) ≠ 0) ∧
  (ggQ2gwDot (E.φ 1) (E.c 2) ≠ 0 ∨ ggQ2gwDot (E.φ 2) (E.c 1) ≠ 0) ∧
  (∀ x : Fin 4 → ZMod 3, (∀ m, ggQ2gwDot (E.φ m) x = 0) → x = 0 ∨ x = E.d ∨ x = -E.d) ∧
  (∀ k, ggQ2gwE k = E.inv k 0 • E.c 0 + E.inv k 1 • E.c 1 + E.inv k 2 • E.c 2 + E.inv k 3 • E.d)

instance (C : Fin 4 → Fin 4 → ZMod 3) (E : GGQ2gwKill) : Decidable (E.OK C) := by
  unfold GGQ2gwKill.OK; infer_instance

end CFSG.StandardType

end
