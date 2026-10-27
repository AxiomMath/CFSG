module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG

namespace FiveTransitive.UniqueTwoFixedPointTransitivity

open MulAction

@[expose] def orbitAction {G X : Type*} [Group G] [MulAction G X] (P : Subgroup G) (x : X) :
    SubMulAction P X where
  carrier := orbit G x
  smul_mem' p _ hz := mem_orbit_of_mem_orbit p.val hz

private theorem mem_fixed_of_orbit_fixed
    {G X : Type*} [Group G] [MulAction G X] (P : Subgroup G) (x : X)
    (z : fixedPoints P (orbitAction P x)) : z.val.val ∈ fixedPoints P X := by
  intro p
  exact congrArg Subtype.val (mem_fixedPoints.mp z.property p)

theorem card_fixed_orbit
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (P : Subgroup G) (x z : X) [Decidable (z ∈ orbit G x)]
    (hfix : fixedPoints P X = {z}) :
    Nat.card (fixedPoints P (orbitAction P x)) = if z ∈ orbit G x then 1 else 0 := by
  classical
  have heq (w : fixedPoints P (orbitAction P x)) : w.val.val = z := by
    have h := mem_fixed_of_orbit_fixed P x w
    rwa [hfix, Set.mem_singleton_iff] at h
  split_ifs with hz
  · apply Nat.card_eq_one_iff_exists.mpr
    have hzfix : z ∈ fixedPoints P X := by rw [hfix]; exact Set.mem_singleton z
    refine ⟨⟨⟨z, hz⟩, ?_⟩, ?_⟩
    · intro p
      apply Subtype.ext
      exact mem_fixedPoints.mp hzfix p
    · intro w
      exact Subtype.ext (Subtype.ext (heq w))
  · let _ : IsEmpty (fixedPoints P (orbitAction P x)) := ⟨fun w =>
      hz ((heq w) ▸ w.val.property)⟩
    exact Nat.card_of_isEmpty

theorem isPretransitive_of_unique_fixed_point
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (hpoint : ∀ x : X, ∃ P : Subgroup G, IsPGroup 2 P ∧ fixedPoints P X = {x}) :
    IsPretransitive G X := by
  classical
  constructor
  intro x y
  suffices hy : y ∈ orbit G x by exact mem_orbit_iff.mp hy
  by_contra hy
  obtain ⟨P, hP, hPx⟩ := hpoint x
  obtain ⟨Q, hQ, hQy⟩ := hpoint y
  have hp := hP.card_modEq_card_fixedPoints (orbitAction P x)
  have hq := hQ.card_modEq_card_fixedPoints (orbitAction Q x)
  change Nat.card (orbit G x) % 2 = Nat.card (fixedPoints P (orbitAction P x)) % 2 at hp
  change Nat.card (orbit G x) % 2 = Nat.card (fixedPoints Q (orbitAction Q x)) % 2 at hq
  rw [card_fixed_orbit P x x hPx, if_pos (mem_orbit_self x)] at hp
  rw [card_fixed_orbit Q x y hQy, if_neg hy] at hq
  omega

end FiveTransitive.UniqueTwoFixedPointTransitivity

end CFSG
