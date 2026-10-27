module

public import Mathlib.Data.Nat.Prime.Factorial
public import CFSG.Permutation.FiveTransitive.NormalizerOrbitFamily

public section

namespace CFSG

namespace FiveTransitive.Degree72LargePrimeOrbitFamily
open MulAction NormalizerOrbitFamily

theorem prime_fixes_family {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (q : ℕ) (hq : q.Prime)
    (Q : Subgroup G) (m : ℕ) (hsmall : Nat.card (Family (X := X) Q m) < q)
    (g : Subgroup.normalizer (Q : Set G)) (hg : g ^ q = 1)
    (O : Family (X := X) Q m) :
    NormalizerOrbitHom.toPermHom (Y := X) Q g O.val = O.val := by
  classical
  let _ : Fact q.Prime := ⟨hq⟩
  let B := Family (X := X) Q m
  let a := NormalizerOrbitFamily.toPermHom (X := X) Q m g
  have ha7 : a ^ q = 1 := by rw [← map_pow,hg,map_one]
  have ha : a = 1 := by
    by_contra hn
    have ho : orderOf a = q := orderOf_eq_prime ha7 hn
    have hd : q ∣ (Nat.card B).factorial := by
      rw [← Nat.card_perm]
      exact ho ▸ orderOf_dvd_natCard a
    exact (not_le_of_gt hsmall) ((Nat.Prime.dvd_factorial hq).mp hd)
  exact congrArg (fun p : Equiv.Perm B => (p O).val) ha

end FiveTransitive.Degree72LargePrimeOrbitFamily

end CFSG
