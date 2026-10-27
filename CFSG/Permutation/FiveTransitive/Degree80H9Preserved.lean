module

public import CFSG.Permutation.FiveTransitive.Degree80H9Pairs
public import CFSG.Permutation.FiveTransitive.Degree67TwoFiveOrbitResidue

public section

namespace CFSG

namespace FiveTransitive.Degree80H9Preserved
open MulAction

theorem preserved_card_eq_two
    {G H X : Type*} [Group G] [Group H] [Finite H] [Fintype X] [MulAction G X]
    (Q : Subgroup G) (hQ : IsPGroup 2 Q) (hX : Nat.card X = 80)
    (i : H →* Subgroup.normalizer (Q : Set G)) (hH : Nat.card H = 9)
    (hpow : ∀ h : H, h ^ 3 = 1) (E : Set X) (hE : E.ncard = 2)
    (hEout : ∀ x ∈ E, x ∉ fixedPoints Q X)
    (hEfix : ∀ h : H, ∀ x ∈ E, (i h).val • x = x)
    (hexact : ∀ h : H, h ≠ 1 → ∀ x : X,
      x ∉ fixedPoints Q X → ((i h).val • x = x ↔ x ∈ E))
    (O : orbitRel.Quotient Q X) (hO : Nat.card O.orbit ≠ 1)
    (h : H) (hh : h ≠ 1)
    (hpres : NormalizerOrbitHom.toPermHom (Y := X) Q (i h) O = O) :
    Nat.card O.orbit = 2 := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hc := Degree80TwoTwelveOrbitMass.orbit_card_cases hX.le Q hQ O
  have hn := Degree80H9Numeric.three_not_dvd (Nat.card O.orbit) (by omega)
  have hi : i h ^ 3 = 1 := by rw [← map_pow,hpow,map_one]
  have hl := Degree67TwoFiveOrbitResidue.preserved_mod_le 3 Q (i h) hi O hpres
  have hp : 0 < Nat.card {x : O.orbit // (i h).val • x.val = x.val} := by omega
  obtain ⟨x⟩ := (Nat.card_pos_iff.mp hp).1
  have hxE : x.val.val ∈ E := (hexact h hh x.val.val
    (Degree52TwoOrbitPreserved.not_fixed_of_mem Q O hO _ x.val.property)).mp x.property
  exact Degree80H9Pairs.orbit_card_eq_two Q hQ hX i hH E hE hEout hEfix hexact
    O x.val.val hxE x.val.property

end FiveTransitive.Degree80H9Preserved

end CFSG
