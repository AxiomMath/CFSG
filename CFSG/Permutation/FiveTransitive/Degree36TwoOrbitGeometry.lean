module

public import CFSG.Permutation.FiveTransitive.NormalizerOrbitFamily
public import Mathlib.GroupTheory.PGroup
import Mathlib.Tactic.Linarith.Frontend

public section

namespace CFSG

namespace FiveTransitive.Degree36TwoOrbitGeometry

open MulAction NormalizerOrbitFamily

theorem orbit_card_two_or_four
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (hX : Nat.card X ≤ 36) (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (g : Subgroup.normalizer (Q : Set G)) (hg : g ^ 5 = 1)
    (hfree : ∀ x : X, x ∉ fixedPoints Q X → g.val • x ≠ x)
    (x : X) (hx : x ∉ fixedPoints Q X) :
    Nat.card (orbit Q x) = 2 ∨ Nat.card (orbit Q x) = 4 := by
  classical
  let _ : Fintype X := Fintype.ofFinite _
  obtain ⟨e,he⟩ := hQ.card_orbit x
  have hm : Nat.card (orbit Q x) ≠ 1 := by
    intro hm
    exact hx (mem_fixedPoints_iff_card_orbit_eq_one.mpr (by rwa [← Nat.card_eq_fintype_card]))
  have hcop : ¬ 5 ∣ Nat.card (orbit Q x) := by
    rw [he]
    intro hd
    have hh := (by decide : Nat.Prime 5).dvd_of_dvd_pow hd
    norm_num at hh
  have hd := five_dvd_card_family Q g hg hfree _ hm hcop
  have hpos : 0 < Nat.card (Family (X := X) Q (Nat.card (orbit Q x))) :=
    Finite.card_pos_iff.mpr ⟨⟨Quotient.mk'' x,by rw [orbitRel.Quotient.orbit_mk]⟩⟩
  have hlo : 5 ≤ Nat.card (Family (X := X) Q (Nat.card (orbit Q x))) := Nat.le_of_dvd hpos hd
  have hb := card_mul_le (X := X) Q (Nat.card (orbit Q x))
  have he2 : e ≤ 2 := by
    by_contra hn
    have hp : 8 ≤ 2 ^ e := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 3 ≤ e)
    rw [he] at hb hlo
    nlinarith
  have he0 : e ≠ 0 := by intro hh; apply hm; rw [he,hh,pow_zero]
  rw [he]
  interval_cases e <;> norm_num at *

theorem family_card_cases
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (hX : Nat.card X = 36) (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (hfixed : Nat.card (fixedPoints Q X) = 6)
    (g : Subgroup.normalizer (Q : Set G)) (hg : g ^ 5 = 1)
    (hfree : ∀ x : X, x ∉ fixedPoints Q X → g.val • x ≠ x) :
    (Nat.card (Family (X := X) Q 2) = 15 ∧ Nat.card (Family (X := X) Q 4) = 0) ∨
    (Nat.card (Family (X := X) Q 2) = 5 ∧ Nat.card (Family (X := X) Q 4) = 5) := by
  classical
  let _ : Fintype X := Fintype.ofFinite _
  have hsize (O : orbitRel.Quotient Q X) :
      Nat.card O.orbit = 1 ∨ Nat.card O.orbit = 2 ∨ Nat.card O.orbit = 4 := by
    refine Quotient.inductionOn O ?_
    intro x
    rw [orbitRel.Quotient.orbit_mk]
    by_cases hx : x ∈ fixedPoints Q X
    · left
      rw [Nat.card_eq_fintype_card]
      exact mem_fixedPoints_iff_card_orbit_eq_one.mp hx
    · exact Or.inr (orbit_card_two_or_four hX.le Q hQ g hg hfree x hx)
  have htotal := card_eq_one_two_four Q hsize
  rw [hX,hfixed] at htotal
  have htwo := five_dvd_card_family Q g hg hfree 2 (by decide) (by decide)
  have hfour := five_dvd_card_family Q g hg hfree 4 (by decide) (by decide)
  omega

end FiveTransitive.Degree36TwoOrbitGeometry

end CFSG
