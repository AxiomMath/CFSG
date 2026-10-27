module

public import CFSG.Permutation.FiveTransitive.Degree67TwoFiveOrbitCount
public import CFSG.Permutation.FiveTransitive.Degree67TwoFiveOrbitResidue

public section

namespace CFSG

namespace FiveTransitive.Degree67TwoFiveGeometry

open MulAction NormalizerOrbitFamily

private theorem numeric (a b c d e f : ℕ)
    (htotal : 62 = 2*a + 4*b + 8*c + 16*d + 32*e + 64*f)
    (ha5 : 2*(a%5) ≤ 2) (hb5 : 4*(b%5) ≤ 2) (hc5 : 3*(c%5) ≤ 2)
    (hd5 : d%5 ≤ 2) (he5 : 2*(e%5) ≤ 2)
    (ha3 : 2*(a%3) ≤ 2) (hc3 : 2*(c%3) ≤ 2) :
    c = 0 ∧ f = 0 ∧
      ((16*d + 32*e = 32 ∧ a = 15 ∧ b = 0) ∨
       (d = 0 ∧ e = 0 ∧ a = 31 ∧ b = 0) ∨
       (d = 0 ∧ e = 0 ∧ a = 21 ∧ b = 5) ∨
       (d = 0 ∧ e = 0 ∧ a = 1 ∧ b = 15)) := by
  have hf : f = 0 := by omega
  have hc : c = 0 := by omega
  have hd3 : d ≤ 3 := by omega
  have hd : d ≤ 2 := by
    rw [Nat.mod_eq_of_lt (by omega : d < 5)] at hd5
    exact hd5
  have he : e ≤ 1 := by omega
  have hb : b = 0 ∨ b = 5 ∨ b = 10 ∨ b = 15 := by omega
  interval_cases d <;> interval_cases e <;> rcases hb with hb | hb | hb | hb <;> omega

theorem orbit_geometry
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (hX : Nat.card X = 67) (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (hfixed : Nat.card (fixedPoints Q X) = 5)
    (g3 g5 : Subgroup.normalizer (Q : Set G)) (hg3 : g3 ^ 3 = 1) (hg5 : g5 ^ 5 = 1)
    (h3 : Nat.card {x : X // x ∉ fixedPoints Q X ∧ g3.val • x = x} ≤ 2)
    (h5 : Nat.card {x : X // x ∉ fixedPoints Q X ∧ g5.val • x = x} ≤ 2) :
    (∀ O : orbitRel.Quotient Q X, Nat.card O.orbit = 1 ∨ Nat.card O.orbit = 2 ∨
      Nat.card O.orbit = 4 ∨ Nat.card O.orbit = 16 ∨ Nat.card O.orbit = 32) ∧
    ((16 * Nat.card (Family (X := X) Q 16) + 32 * Nat.card (Family (X := X) Q 32) = 32 ∧
        Nat.card (Family (X := X) Q 2) = 15 ∧ Nat.card (Family (X := X) Q 4) = 0) ∨
     (Nat.card (Family (X := X) Q 16) = 0 ∧ Nat.card (Family (X := X) Q 32) = 0 ∧
        Nat.card (Family (X := X) Q 2) = 31 ∧ Nat.card (Family (X := X) Q 4) = 0) ∨
     (Nat.card (Family (X := X) Q 16) = 0 ∧ Nat.card (Family (X := X) Q 32) = 0 ∧
        Nat.card (Family (X := X) Q 2) = 21 ∧ Nat.card (Family (X := X) Q 4) = 5) ∨
     (Nat.card (Family (X := X) Q 16) = 0 ∧ Nat.card (Family (X := X) Q 32) = 0 ∧
        Nat.card (Family (X := X) Q 2) = 1 ∧ Nat.card (Family (X := X) Q 4) = 15)) := by
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  have ht := Degree67TwoFiveOrbitCount.card_eq_orbit_sum hX.le Q hQ
  rw [hX,hfixed] at ht
  have hn := numeric (Nat.card (Family (X := X) Q 2)) (Nat.card (Family (X := X) Q 4))
    (Nat.card (Family (X := X) Q 8)) (Nat.card (Family (X := X) Q 16))
    (Nat.card (Family (X := X) Q 32)) (Nat.card (Family (X := X) Q 64)) (by omega)
    (Degree67TwoFiveOrbitResidue.family_residue_bound 5 Q g5 hg5 2 h5 2 (by decide))
    (Degree67TwoFiveOrbitResidue.family_residue_bound 5 Q g5 hg5 2 h5 4 (by decide))
    (Degree67TwoFiveOrbitResidue.family_residue_bound 5 Q g5 hg5 2 h5 8 (by decide))
    (by simpa using Degree67TwoFiveOrbitResidue.family_residue_bound 5 Q g5 hg5 2 h5 16 (by decide))
    (Degree67TwoFiveOrbitResidue.family_residue_bound 5 Q g5 hg5 2 h5 32 (by decide))
    (Degree67TwoFiveOrbitResidue.family_residue_bound 3 Q g3 hg3 2 h3 2 (by decide))
    (Degree67TwoFiveOrbitResidue.family_residue_bound 3 Q g3 hg3 2 h3 8 (by decide))
  refine ⟨?_,hn.2.2⟩
  intro O
  have h8 : Nat.card O.orbit ≠ 8 := by
    intro he
    have hp : 0 < Nat.card (Family (X := X) Q 8) := Finite.card_pos_iff.mpr ⟨⟨O,he⟩⟩
    omega
  have h64 : Nat.card O.orbit ≠ 64 := by
    intro he
    have hp : 0 < Nat.card (Family (X := X) Q 64) := Finite.card_pos_iff.mpr ⟨⟨O,he⟩⟩
    omega
  have hc := Degree67TwoFiveOrbitCount.orbit_card_cases hX.le Q hQ O
  omega

end FiveTransitive.Degree67TwoFiveGeometry

end CFSG
