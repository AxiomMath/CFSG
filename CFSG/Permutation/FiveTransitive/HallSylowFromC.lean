module

public import CFSG.Permutation.FiveTransitive.HallOrbitTransitivity
public import CFSG.Permutation.FiveTransitive.HallSylowNormalizer

public section

namespace CFSG

namespace FiveTransitive.Research.HallSylowFromC

open MulAction Subgroup
open Research.HallOrbitTransitivity
open Research.HallSylowNormalizer

variable {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X]

@[expose] def sylowImage {p : ℕ} (C : Subgroup G) (P : Sylow p C) : Subgroup G :=
  Subgroup.map C.subtype (P : Subgroup C)

theorem sylowImage_isPGroup
    {p : ℕ} [Fact p.Prime]
    (C : Subgroup G) (P : Sylow p C) :
    IsPGroup p (sylowImage C P) := by
  exact P.isPGroup'.map C.subtype

theorem orbit_sylowImage_eq
    {p : ℕ} (C : Subgroup G) (P : Sylow p C) (x : X) :
    MulAction.orbit (sylowImage C P) x = MulAction.orbit P x := by
  ext z
  simp only [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨u, hu, hug⟩ := g.prop
    let v : P := ⟨u, hu⟩
    refine ⟨v, ?_⟩
    change (u : G) • x = z
    change (g : G) • x = z at hg
    change (u : G) = (g : G) at hug
    rw [hug]
    exact hg
  · rintro ⟨u, hu⟩
    let g : sylowImage C P :=
      ⟨((u : C) : G), ⟨(u : C), u.prop, rfl⟩⟩
    refine ⟨g, ?_⟩
    change ((u : C) : G) • x = z
    exact hu

theorem exists_ambientSylow_containing_sylowImage
    {p : ℕ} [Fact p.Prime]
    (e : Fin 4 ↪ X) (C : Subgroup G)
    (hCbase : C ≤ MulAction.stabilizer G e)
    (P : Sylow p C) :
    ∃ Q : Sylow p (MulAction.stabilizer G e),
      sylowImage C P ≤ ambientSylow e Q := by
  let f : C →* MulAction.stabilizer G e := Subgroup.inclusion hCbase
  let PH : Subgroup (MulAction.stabilizer G e) :=
    Subgroup.map f (P : Subgroup C)
  have hPH : IsPGroup p PH := P.isPGroup'.map f
  obtain ⟨Q, hQ⟩ := hPH.exists_le_sylow
  refine ⟨Q, ?_⟩
  rintro g ⟨u, huP, rfl⟩
  have huf : f u ∈ (Q : Subgroup (MulAction.stabilizer G e)) :=
    hQ ⟨u, huP, rfl⟩
  exact ⟨f u, huf, rfl⟩

theorem exceptional_subset_fixedPoints_sylowImage
    {p : ℕ} (C : Subgroup G) (P : Sylow p C) (E : Set X)
    (hCfix : ∀ c : C, ∀ x ∈ E, (c : G) • x = x) :
    E ⊆ MulAction.fixedPoints (sylowImage C P) X := by
  intro x hx
  rw [MulAction.mem_fixedPoints]
  rintro z
  obtain ⟨u, _huP, huz⟩ := z.prop
  change (z : G) • x = x
  rw [← huz]
  exact hCfix u x hx

theorem outside_moved_by_sylowImage
    {p : ℕ} [Fact p.Prime]
    (C : Subgroup G) (P : Sylow p C) (E : Set X)
    (horbit : ∀ x, x ∉ E → p ∣ (MulAction.orbit C x).ncard) :
    ∀ x, x ∉ E → ∃ z : sylowImage C P, z • x ≠ x := by
  intro x hx
  obtain ⟨u, hu⟩ :=
    exists_sylow_element_moves_of_prime_dvd_orbit C P x (horbit x hx)
  let z : sylowImage C P :=
    ⟨(u : C), ⟨u, u.prop, rfl⟩⟩
  exact ⟨z, hu⟩

theorem exists_prime_ne_three_dvd_or_eq_three_pow
    (t : ℕ) (ht : 2 ≤ t) :
    (∃ p, Nat.Prime p ∧ p ∣ t ∧ p ≠ 3) ∨
      ∃ w, 0 < w ∧ t = 3 ^ w := by
  classical
  by_cases h : ∃ p, Nat.Prime p ∧ p ∣ t ∧ p ≠ 3
  · exact Or.inl h
  · right
    have hprime : ∀ {p}, Nat.Prime p → p ∣ t → p = 3 := by
      intro p hp hpt
      by_contra hp3
      exact h ⟨p, hp, hpt, hp3⟩
    have ht0 : t ≠ 0 := by omega
    let w := t.primeFactorsList.length
    have hpow : t = 3 ^ w :=
      Nat.eq_prime_pow_of_unique_prime_dvd ht0 hprime
    refine ⟨w, ?_, hpow⟩
    by_contra hw
    have hw0 : w = 0 := by omega
    rw [hw0, pow_zero] at hpow
    omega

end FiveTransitive.Research.HallSylowFromC

end CFSG
