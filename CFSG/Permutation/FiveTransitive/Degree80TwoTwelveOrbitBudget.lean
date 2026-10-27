module

public import CFSG.Permutation.FiveTransitive.NormalizerRigidOrbitResidueSum
public import CFSG.Permutation.FiveTransitive.TwoGroupSixtyFourOrbitElevenFixed
public import CFSG.Permutation.FiveTransitive.Degree80TwoTwelveOrbitMass
public import CFSG.Permutation.FiveTransitive.Degree80LargePrimeFixity

public section

namespace CFSG

namespace FiveTransitive.Degree80TwoTwelveOrbitBudget
open MulAction NormalizerOrbitFamily
open scoped BigOperators

theorem residue_budget
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 80)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 2 Q)
    (g : Subgroup.normalizer (Q : Set P)) (hg : orderOf g = 11) :
    2 * (Nat.card (Family (X := X) Q 2) % 11) +
      4 * (Nat.card (Family (X := X) Q 4) % 11) +
      8 * (Nat.card (Family (X := X) Q 8) % 11) +
      16 * (Nat.card (Family (X := X) Q 16) % 11) +
      32 * (Nat.card (Family (X := X) Q 32) % 11) +
      64 * (Nat.card (Family (X := X) Q 64) % 11) ≤ 3 := by
  classical
  let _ : Fact (Nat.Prime 11) := ⟨by decide⟩
  have hfix (m : ℕ) (_ : m ∈ ({2,4,8,16,32,64} : Finset ℕ)) (O : Family (X := X) Q m)
      (hO : NormalizerOrbitFamily.toPermHom (X := X) Q m g O = O)
      (x : O.val.orbit) : g.val • x.val = x.val := by
    have he : (Quotient.mk'' x.val : orbitRel.Quotient Q X) = O.val :=
      orbitRel.Quotient.mem_orbit.mp x.property
    have hsmall : Nat.card (orbit Q x.val) ≤ 64 := by
      have hc := Degree80TwoTwelveOrbitMass.orbit_card_cases
        (by rw [Nat.card_eq_fintype_card,hcard]) Q hQ (Quotient.mk'' x.val)
      rw [orbitRel.Quotient.orbit_mk] at hc
      omega
    have hpres : NormalizerOrbitHom.toPermHom (Y := X) Q g O.val = O.val :=
      congrArg Subtype.val hO
    have hgx : g.val • x.val ∈ orbit Q x.val := by
      apply Quotient.exact (s := orbitRel Q X)
      change NormalizerOrbitHom.toPermHom (Y := X) Q g (Quotient.mk'' x.val) = Quotient.mk'' x.val
      rwa [he]
    exact TwoGroupSixtyFourOrbitElevenFixed.fixes_preserved_orbit Q hQ g.val g.property
      (congrArg Subtype.val (hg ▸ pow_orderOf_eq_one g)) x.val hsmall hgx x.val (mem_orbit_self _)
  have hl := NormalizerRigidOrbitResidueSum.sum_le 11 Q g (hg ▸ pow_orderOf_eq_one g)
    {2,4,8,16,32,64} hfix
  norm_num only [Finset.sum_insert,Finset.mem_insert,Finset.mem_singleton,Finset.sum_singleton,
    or_self,not_false_eq_true] at hl
  have hglobal := Degree80LargePrimeFixity.eleven_fixed_card_eq_three P hcard h5 hnotAlt g.val
    ((Subgroup.orderOf_coe g).trans hg)
  change Nat.card (fixedBy X g.val) = 3 at hglobal
  rw [hglobal] at hl
  omega

end FiveTransitive.Degree80TwoTwelveOrbitBudget

end CFSG
