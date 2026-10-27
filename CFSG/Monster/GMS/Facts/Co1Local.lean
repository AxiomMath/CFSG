
module

public import CFSG.Monster.GMS.Facts.Co1Module
public import CFSG.Sporadic.Co1.Module.OrbitsBase

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

@[expose] def co1Stab (v : Fin 24 → ZMod 2) : Subgroup Co1 where
  carrier := {g | co1Act g v = v}
  mul_mem' {g h} hg hh := by
    simp only [Set.mem_ofPred_eq] at hg hh ⊢
    rw [map_mul, Module.End.mul_apply, hh, hg]
  one_mem' := by
    simp only [Set.mem_ofPred_eq, map_one, Module.End.one_apply]
  inv_mem' {g} hg := by
    simp only [Set.mem_ofPred_eq] at hg ⊢
    conv_lhs => rw [← hg]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

@[expose] def co1Fix (g : Co1) : Set (Fin 24 → ZMod 2) := {v | co1Act g v = v}

@[expose] def co1Orbit (i : Fin 3) : Set (Fin 24 → ZMod 2) :=
  Set.range fun g : Co1 => co1Act g (CFSG.Sporadic.Co1.Module.reps i)

@[expose] def Co1PairFacts : Prop :=
  (∀ x ∈ co1Orbit 0, ∃ y ∈ co1Orbit 0, x + y ∈ co1Orbit 0 ∧
    3 ^ 6 * 11 ∣ Nat.card ↥(co1Stab x ⊓ co1Stab y)) ∧
  (∀ x ∈ co1Orbit 0, ∃ y ∈ co1Orbit 2, x + y ∈ co1Orbit 0 ∧
    2 ^ 18 ∣ Nat.card ↥(co1Stab x ⊓ co1Stab y)) ∧
  (∀ x ∈ co1Orbit 0, ∃ y ∈ co1Orbit 2, x + y ∈ co1Orbit 2) ∧
  (∀ x y x' y', x ∈ co1Orbit 0 → y ∈ co1Orbit 0 → x + y ∈ co1Orbit 1 →
    x' ∈ co1Orbit 0 → y' ∈ co1Orbit 0 → x' + y' ∈ co1Orbit 1 →
      ∃ g : Co1, co1Act g x = x' ∧ co1Act g y = y') ∧
  (∀ x y, x ∈ co1Orbit 0 → y ∈ co1Orbit 0 → x + y ∈ co1Orbit 1 →
    Nat.card ↥(co1Stab x ⊓ co1Stab y) = 2 ^ 7 * 3 ^ 6 * 5 ^ 3 * 7 * 11) ∧
  (∀ x y w, x ∈ co1Orbit 0 → y ∈ co1Orbit 0 → x + y ∈ co1Orbit 1 → w ∈ co1Orbit 0 →
    x + w ∈ co1Orbit 0 → w + y ∈ co1Orbit 0 →
      Nat.card ↥(co1Stab x ⊓ co1Stab w ⊓ co1Stab y) = 2 ^ 7 * 3 ^ 6 * 5 * 7)

@[expose] def Co1InvolutionFacts : Prop :=
  (∀ s : Co1, orderOf s = 2 →
    (co1Fix s).ncard * Nat.card ↥(Subgroup.centralizer ({s} : Set Co1)) ≤
        2 ^ 37 * 3 ^ 5 * 5 ^ 2 * 7 ∧
      ((co1Fix s).ncard * Nat.card ↥(Subgroup.centralizer ({s} : Set Co1)) =
        2 ^ 37 * 3 ^ 5 * 5 ^ 2 * 7 → (co1Fix s).ncard = 2 ^ 16)) ∧
  (∀ r s : Co1, orderOf r = 2 → orderOf s = 2 →
    (co1Fix r).ncard * Nat.card ↥(Subgroup.centralizer ({r} : Set Co1)) =
      2 ^ 37 * 3 ^ 5 * 5 ^ 2 * 7 →
      ∃ g : Co1, ∀ k : ℕ, orderOf (g * r * g⁻¹ * s) ≠ 2 ^ k) ∧
  (∀ r r' : Co1, orderOf r = 2 → orderOf r' = 2 →
    (co1Fix r).ncard * Nat.card ↥(Subgroup.centralizer ({r} : Set Co1)) =
      2 ^ 37 * 3 ^ 5 * 5 ^ 2 * 7 →
    (co1Fix r').ncard * Nat.card ↥(Subgroup.centralizer ({r'} : Set Co1)) =
      2 ^ 37 * 3 ^ 5 * 5 ^ 2 * 7 → IsConj r r')

end CFSG.Monster.GMS
