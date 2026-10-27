module

public import CFSG.Permutation.FiveTransitive.NormalizerOrbitFamily
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG

namespace FiveTransitive.TwoGroupOrbitCount

open MulAction NormalizerOrbitFamily
open scoped BigOperators

theorem orbit_card_cases
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (hX : Nat.card X ≤ 127) (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (O : orbitRel.Quotient Q X) :
    Nat.card O.orbit = 1 ∨ Nat.card O.orbit = 2 ∨ Nat.card O.orbit = 4 ∨
      Nat.card O.orbit = 8 ∨ Nat.card O.orbit = 16 ∨ Nat.card O.orbit = 32 ∨ Nat.card O.orbit = 64 := by
  refine Quotient.inductionOn O ?_
  intro x
  rw [orbitRel.Quotient.orbit_mk]
  obtain ⟨e,he⟩ := hQ.card_orbit x
  have hb := Nat.card_le_card_of_injective (fun y : orbit Q x => y.val) Subtype.val_injective
  have he7 : e ≤ 6 := by
    by_contra hn
    have hp : 128 ≤ 2 ^ e := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 7 ≤ e)
    rw [he] at hb
    omega
  rw [he]
  interval_cases e <;> norm_num

theorem card_eq_orbit_sum
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (hX : Nat.card X ≤ 127) (Q : Subgroup G) (hQ : IsPGroup 2 Q) :
    Nat.card X = Nat.card (fixedPoints Q X) +
      2 * Nat.card (Family (X := X) Q 2) + 4 * Nat.card (Family (X := X) Q 4) +
      8 * Nat.card (Family (X := X) Q 8) + 16 * Nat.card (Family (X := X) Q 16) +
      32 * Nat.card (Family (X := X) Q 32) +
      64 * Nat.card (Family (X := X) Q 64) := by
  classical
  let _ : Fintype X := Fintype.ofFinite _
  let _ : Fintype (orbitRel.Quotient Q X) := Fintype.ofFinite _
  have he : Nat.card X = ∑ O : orbitRel.Quotient Q X, Nat.card O.orbit := by
    rw [Nat.card_congr (selfEquivSigmaOrbits Q X)]
    simp only [Nat.card_eq_fintype_card,Fintype.card_sigma]
    congr 1
    funext O
    rw [orbitRel.Quotient.orbit_eq_orbit_out O Quotient.out_eq']
  have hcount (m : ℕ) : Nat.card (Family (X := X) Q m) =
      ∑ O : orbitRel.Quotient Q X, if Nat.card O.orbit = m then 1 else 0 := by
    simp only [Family,Nat.card_eq_fintype_card,Fintype.card_subtype,
      Finset.card_eq_sum_ones,Finset.sum_filter]
  have hterm (O : orbitRel.Quotient Q X) : Nat.card O.orbit =
      (if Nat.card O.orbit = 1 then 1 else 0) +
      2 * (if Nat.card O.orbit = 2 then 1 else 0) +
      4 * (if Nat.card O.orbit = 4 then 1 else 0) +
      8 * (if Nat.card O.orbit = 8 then 1 else 0) +
      16 * (if Nat.card O.orbit = 16 then 1 else 0) +
      32 * (if Nat.card O.orbit = 32 then 1 else 0) +
      64 * (if Nat.card O.orbit = 64 then 1 else 0) := by
    rcases orbit_card_cases hX Q hQ O with h | h | h | h | h | h | h
      <;> rw [h] <;> norm_num
  rw [he]
  calc
    ∑ O : orbitRel.Quotient Q X, Nat.card O.orbit =
        ∑ O : orbitRel.Quotient Q X,
          ((if Nat.card O.orbit = 1 then 1 else 0) +
          2 * (if Nat.card O.orbit = 2 then 1 else 0) +
          4 * (if Nat.card O.orbit = 4 then 1 else 0) +
          8 * (if Nat.card O.orbit = 8 then 1 else 0) +
          16 * (if Nat.card O.orbit = 16 then 1 else 0) +
          32 * (if Nat.card O.orbit = 32 then 1 else 0) +
          64 * (if Nat.card O.orbit = 64 then 1 else 0)) :=
      Finset.sum_congr rfl (fun O _ => hterm O)
    _ = _ := by
      simp only [Finset.sum_add_distrib,← Finset.mul_sum,← hcount,fixed_family_card]

end FiveTransitive.TwoGroupOrbitCount

end CFSG
