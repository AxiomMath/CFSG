module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG

namespace FiveTransitive.SylowTwoSmallOrbit

open MulAction

private theorem two_not_dvd_orbit_card
    {G X : Type*} [Group G] [Finite G] [MulAction G X]
    (P : Sylow 2 G) (x : X) (hP : ∀ p : P, (p : G) • x = x) :
    ¬ 2 ∣ Nat.card (orbit G x) := by
  have hle : (P : Subgroup G) ≤ stabilizer G x := fun p hp => hP ⟨p, hp⟩
  have hd := Subgroup.index_dvd_of_le hle
  rw [index_stabilizer, ← Nat.card_coe_set_eq] at hd
  exact fun h => P.not_dvd_index (h.trans hd)

private theorem smul_eq_of_orbit_card_le_two
    {G X : Type*} [Group G] [Finite G] [MulAction G X]
    (P : Sylow 2 G) (x : X) (hP : ∀ p : P, (p : G) • x = x)
    (hsmall : Nat.card (orbit G x) ≤ 2) : ∀ g : G, g • x = x := by
  have hodd := two_not_dvd_orbit_card P x hP
  have hcard : Nat.card (orbit G x) = 1 := by
    have hmod := Nat.mod_lt (Nat.card (orbit G x)) (by decide : 0 < 2)
    have hn : Nat.card (orbit G x) % 2 ≠ 0 := fun h => hodd (Nat.dvd_of_mod_eq_zero h)
    omega
  let _ : Subsingleton (orbit G x) := (Nat.card_eq_one_iff_unique.mp hcard).1
  intro g
  exact congrArg Subtype.val (Subsingleton.elim
    (⟨g • x, mem_orbit x g⟩ : orbit G x) ⟨x, mem_orbit_self x⟩)

theorem smul_eq_of_smul_eq_or
    {G X : Type*} [Group G] [Finite G] [MulAction G X]
    (P : Sylow 2 G) (x y : X) (hP : ∀ p : P, (p : G) • x = x)
    (horbit : ∀ g : G, g • x = x ∨ g • x = y) : ∀ g : G, g • x = x := by
  apply smul_eq_of_orbit_card_le_two P x hP
  rw [Nat.card_coe_set_eq]
  have hsub : orbit G x ⊆ ({x, y} : Set X) := by
    intro z hz
    obtain ⟨g, rfl⟩ := mem_orbit_iff.mp hz
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using horbit g
  have hle := Set.ncard_le_ncard hsub
  have hpair : ({x, y} : Set X).ncard ≤ 2 := by
    classical
    by_cases h : x = y
    · simp [h]
    · simp [Set.ncard_pair h]
  exact hle.trans hpair

end FiveTransitive.SylowTwoSmallOrbit

end CFSG
