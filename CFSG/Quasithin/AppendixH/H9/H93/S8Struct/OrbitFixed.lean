module

public import CFSG.Quasithin.AppendixH.H9.H93.S8Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.ASVolI.ChH

namespace ElemAb2Orbits

open Equiv

variable {E : Subgroup (Perm (Fin 8))}

theorem apply_comm_of_isElemAb2 (hE : IsElemAb2 E) {e g : Perm (Fin 8)} (he : e ∈ E)
    (hg : g ∈ E) (y : Fin 8) : e (g y) = g (e y) :=
  congrArg (fun p : Perm (Fin 8) => p y) (hE.1 e he g hg)

theorem apply_eq_self_of_mem_orbit (hE : IsElemAb2 E) {e : Perm (Fin 8)} (he : e ∈ E)
    {x y : Fin 8} (hx : e x = x) (hy : y ∈ MulAction.orbit E x) : e y = y := by
  obtain ⟨⟨g, hg⟩, rfl⟩ := MulAction.mem_orbit_iff.mp hy
  change e (g x) = g x
  rw [apply_comm_of_isElemAb2 hE he hg, hx]

theorem apply_mem_orbit_of_mem {e : Perm (Fin 8)} (he : e ∈ E) {x y : Fin 8}
    (hy : y ∈ MulAction.orbit E x) : e y ∈ MulAction.orbit E x := by
  obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hy
  exact MulAction.mem_orbit_iff.mpr ⟨⟨e, he⟩ * g, by simp [mul_smul]⟩

theorem orbit_local_of_mem (hE : IsElemAb2 E) {σ : Perm (Fin 8)} (hσ : σ ∈ E) (x : Fin 8) :
    (∀ y ∈ MulAction.orbit E x, σ y ∈ MulAction.orbit E x) ∧
      ((∀ y ∈ MulAction.orbit E x, σ y = y) ∨
        ∀ y ∈ MulAction.orbit E x, σ y ≠ y ∧ σ (σ y) = y) := by
  refine ⟨fun y hy => apply_mem_orbit_of_mem hσ hy, ?_⟩
  by_cases hfix : ∃ y ∈ MulAction.orbit E x, σ y = y
  · obtain ⟨y, hy, hσy⟩ := hfix
    left
    intro z hz
    refine apply_eq_self_of_mem_orbit hE hσ hσy ?_
    rwa [MulAction.orbit_eq_iff.mpr hy]
  · right
    push Not at hfix
    intro y hy
    refine ⟨hfix y hy, ?_⟩
    have h2 : (σ ^ 2) y = y := by rw [hE.2 σ hσ]; rfl
    simpa [pow_two] using h2

theorem ncard_orbit_cases (hE : IsElemAb2 E) (x : Fin 8) :
    (MulAction.orbit E x).ncard = 1 ∨ (MulAction.orbit E x).ncard = 2 ∨
      (MulAction.orbit E x).ncard = 4 ∨ (MulAction.orbit E x).ncard = 8 := by
  have hp : IsPGroup 2 E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 g g.2)⟩
  obtain ⟨n, hn⟩ := hp.card_orbit x
  rw [Nat.card_coe_set_eq] at hn
  have hle : (MulAction.orbit E x).ncard ≤ 8 := by
    simpa using Set.ncard_le_card (MulAction.orbit E x)
  rw [hn] at hle ⊢
  have hn4 : n < 4 := by
    by_contra h
    push Not at h
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) h
    omega
  interval_cases n <;> simp

end ElemAb2Orbits

end CFSG.ASVolI.ChH
