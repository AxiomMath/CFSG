module

public import CFSG.Permutation.FiveTransitive.Degree72LargePrimeOrbitRigidity
public import CFSG.Permutation.FiveTransitive.Degree72LargePrimeOrbitFamily

public section

namespace CFSG

namespace FiveTransitive.PrimeOrbitNormalizerSupport
open MulAction

theorem support_le_fixed
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpq : p.Coprime q) (hqpred : ¬ q ∣ p - 1)
    (Q : Subgroup P) (hQ : IsPGroup p Q)
    (horbit : ∀ x : X, x ∉ fixedPoints Q X → Nat.card (orbit Q x) = p)
    (hfamily : Nat.card (NormalizerOrbitFamily.Family (X := X) Q p) < q)
    (z : Subgroup.normalizer (Q : Set P)) (hz : z ^ q = 1) :
    z.val.val.support.card ≤ Nat.card (fixedPoints Q X) := by
  classical
  have hfix (x : X) (hx : x ∉ fixedPoints Q X) : z.val • x = x := by
    have ho := horbit x hx
    let O : NormalizerOrbitFamily.Family (X := X) Q p :=
      ⟨Quotient.mk'' x,by simpa only [orbitRel.Quotient.orbit_mk] using ho⟩
    have he := Degree72LargePrimeOrbitFamily.prime_fixes_family q hq Q p hfamily z hz O
    have horbit : z.val • x ∈ orbit Q x := Quotient.exact he
    exact Degree72LargePrimeOrbitRigidity.fixes_preserved_orbit p q hp hq hpq hqpred
      Q hQ z.val z.property (congrArg Subtype.val hz) x ho.le horbit x (mem_orbit_self x)
  have hsub : (z.val.val.support : Set X) ⊆ fixedPoints Q X := by
    intro x hx
    by_contra hn
    exact (Equiv.Perm.mem_support.mp hx) (hfix x hn)
  have hh := Set.ncard_le_ncard hsub
  rw [Set.ncard_coe_finset,← Nat.card_coe_set_eq] at hh
  exact hh

end FiveTransitive.PrimeOrbitNormalizerSupport

end CFSG
