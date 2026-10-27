module

public import CFSG.Permutation.FiveTransitive.NormalizerOrbitFamily
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG

namespace FiveTransitive.Degree54TwoOrbitPreserved

open MulAction NormalizerOrbitFamily

theorem orbit_card_cases
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (hX : Nat.card X ≤ 54) (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (O : orbitRel.Quotient Q X) :
    Nat.card O.orbit = 1 ∨ Nat.card O.orbit = 2 ∨ Nat.card O.orbit = 4 ∨
      Nat.card O.orbit = 8 ∨ Nat.card O.orbit = 16 ∨ Nat.card O.orbit = 32 := by
  refine Quotient.inductionOn O ?_
  intro x
  rw [orbitRel.Quotient.orbit_mk]
  obtain ⟨e,he⟩ := hQ.card_orbit x
  have hb := Nat.card_le_card_of_injective (fun y : orbit Q x => y.val) Subtype.val_injective
  have he6 : e ≤ 5 := by
    by_contra hn
    have hp : 64 ≤ 2 ^ e := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 6 ≤ e)
    rw [he] at hb
    omega
  rw [he]
  interval_cases e <;> norm_num

end FiveTransitive.Degree54TwoOrbitPreserved

end CFSG
