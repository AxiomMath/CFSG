module

public import CFSG.Permutation.FiveTransitive.Degree67TwoFiveGeometry
public import CFSG.Permutation.FiveTransitive.Degree67TwoFiveEasyBounds

public section

namespace CFSG

namespace FiveTransitive.Degree67TwoFiveReduction
open MulAction NormalizerOrbitFamily

private theorem orbit_ne_of_family_zero
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (Q : Subgroup G) (m : ℕ) (hc : Nat.card (Family (X := X) Q m) = 0) (x : X) :
    Nat.card (orbit Q x) ≠ m := by
  intro he
  have hp : 0 < Nat.card (Family (X := X) Q m) :=
    Finite.card_pos_iff.mpr ⟨⟨Quotient.mk'' x,by rwa [orbitRel.Quotient.orbit_mk]⟩⟩
  omega

theorem easy_or_hard
    {G X : Type*} [Group G] [Finite G] [MulAction G X] [Fintype X]
    (hX : Fintype.card X = 67) (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (hF : Nat.card (fixedPoints Q X) = 5)
    (g3 g5 : Subgroup.normalizer (Q : Set G)) (hg3 : g3 ^ 3 = 1) (hg5 : g5 ^ 5 = 1)
    (h3 : Nat.card {x : X // x ∉ fixedPoints Q X ∧ g3.val • x = x} ≤ 2)
    (h5 : Nat.card {x : X // x ∉ fixedPoints Q X ∧ g5.val • x = x} ≤ 2)
    (hbound : ∀ q : Q, q ≠ 1 → Nat.card (fixedBy X q) ≤ 33) :
    Nat.card Q ≤ 65536 ∨ ((∀ x : X, Nat.card (orbit Q x) ≤ 4) ∧
      Nat.card (Family (X := X) Q 2) = 1 ∧ Nat.card (Family (X := X) Q 4) = 15) := by
  have hn : Nat.card X = 67 := by rwa [Nat.card_eq_fintype_card]
  obtain ⟨hsize,hcases⟩ := Degree67TwoFiveGeometry.orbit_geometry hn Q hQ hF g3 g5 hg3 hg5 h3 h5
  have hpoint (x : X) : Nat.card (orbit Q x) = 1 ∨ Nat.card (orbit Q x) = 2 ∨
      Nat.card (orbit Q x) = 4 ∨ Nat.card (orbit Q x) = 16 ∨ Nat.card (orbit Q x) = 32 := by
    simpa only [orbitRel.Quotient.orbit_mk] using hsize (Quotient.mk'' x)
  have hsmall (h16 : Nat.card (Family (X := X) Q 16) = 0)
      (h32 : Nat.card (Family (X := X) Q 32) = 0) (x : X) :
      Nat.card (orbit Q x) = 1 ∨ Nat.card (orbit Q x) = 2 ∨ Nat.card (orbit Q x) = 4 := by
    have h16x := orbit_ne_of_family_zero Q 16 h16 x
    have h32x := orbit_ne_of_family_zero Q 32 h32 x
    rcases hpoint x with h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact False.elim (h16x h)
    · exact False.elim (h32x h)
  rcases hcases with ⟨_,hpair,_⟩ | ⟨h16,h32,_,hquad⟩ |
      ⟨h16,h32,_,hquad⟩ | ⟨h16,h32,hpair,hquad⟩
  · exact Or.inl ((Degree67TwoFiveEasyBounds.fifteen_pairs_card_le Q hQ hF hpair hbound).trans
      (by decide))
  · have horbit (x : X) : Nat.card (orbit Q x) ≤ 2 := by
      have hx := hsmall h16 h32 x
      have h4 := orbit_ne_of_family_zero Q 4 hquad x
      omega
    exact Or.inl ((Degree67TwoFiveEasyBounds.pairs_card_le hX Q hF horbit hbound).trans (by decide))
  · exact Or.inl (Degree67TwoFiveEasyBounds.five_quads_card_le hX Q hQ hF hquad
      (hsmall h16 h32) hbound)
  · exact Or.inr ⟨fun x => by have hx := hsmall h16 h32 x; omega,hpair,hquad⟩

end FiveTransitive.Degree67TwoFiveReduction

end CFSG
