module

public import CFSG.Permutation.FiveTransitive.SylowThreeFixedOrbits
public import Mathlib.GroupTheory.GroupAction.Blocks

public section

namespace CFSG

namespace FiveTransitive.OddNormalSylowTransitive

open MulAction

private theorem orbit_meets_fixed_points
    (G X : Type*) [Group G] [Finite G] [MulAction G X] [Finite X]
    [IsPretransitive G X] (N : Subgroup G) [N.Normal]
    (S : Sylow 2 N) (hodd : Odd (Nat.card X)) (x : X) :
    ∃ z : fixedPoints S X, z.val ∈ orbit N x := by
  have hd : Nat.card (orbit N x) ∣ Nat.card X := by
    rw [Nat.card_coe_set_eq]
    exact (IsBlock.orbit_of_normal (N := N) x).ncard_dvd_card ⟨x, mem_orbit_self x⟩
  have ho : ¬ 2 ∣ Nat.card (orbit N x) := (hodd.of_dvd_nat hd).not_two_dvd_nat
  let O := SylowThreeFixedOrbits.orbitAction (S : Subgroup N) x
  have hm := S.isPGroup'.card_modEq_card_fixedPoints O
  have hnonzero : Nat.card (fixedPoints S O) ≠ 0 := by
    intro he
    change Nat.card (orbit N x) % 2 = Nat.card (fixedPoints S O) % 2 at hm
    rw [he, Nat.zero_mod] at hm
    exact ho (Nat.dvd_of_mod_eq_zero hm)
  obtain ⟨z⟩ : Nonempty (fixedPoints S O) := Finite.card_pos_iff.mp (Nat.pos_of_ne_zero hnonzero)
  refine ⟨⟨z.val.val, ?_⟩, z.val.property⟩
  rw [mem_fixedPoints]
  intro q
  exact congrArg Subtype.val (mem_fixedPoints.mp z.property q)

theorem isPretransitive_of_fixed_points
    (G X : Type*) [Group G] [Finite G] [MulAction G X] [Finite X]
    [IsPretransitive G X] (N : Subgroup G) [N.Normal]
    (S : Sylow 2 N) (hodd : Odd (Nat.card X))
    (hconnect : ∀ u v : fixedPoints S X, ∃ n : N, n • u.val = v.val) :
    IsPretransitive N X := by
  constructor
  intro x y
  obtain ⟨u, hu⟩ := orbit_meets_fixed_points G X N S hodd x
  obtain ⟨v, hv⟩ := orbit_meets_fixed_points G X N S hodd y
  obtain ⟨g, hg⟩ := hu
  obtain ⟨h, hh⟩ := hv
  obtain ⟨n, hn⟩ := hconnect u v
  change g • x = u.val at hg
  change h • y = v.val at hh
  refine ⟨h⁻¹ * n * g, ?_⟩
  rw [mul_smul, mul_smul, hg, hn, ← hh, inv_smul_smul]

end FiveTransitive.OddNormalSylowTransitive

end CFSG
