module

public import CFSG.Permutation.FiveTransitive.NormalizerOrbitFamily

public section

namespace CFSG

namespace FiveTransitive.NormalizerExteriorOrbitFamilyFive

open MulAction NormalizerOrbitFamily

theorem five_fixes_family {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (Q : Subgroup G) (m : ℕ) (hsmall : Nat.card (Family (X := X) Q m) ≤ 4)
    (g : Subgroup.normalizer (Q : Set G)) (hg : g ^ 5 = 1)
    (O : Family (X := X) Q m) :
    NormalizerOrbitHom.toPermHom (Y := X) Q g O.val = O.val := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let B := Family (X := X) Q m
  let a := NormalizerOrbitFamily.toPermHom (X := X) Q m g
  have ha7 : a ^ 5 = 1 := by rw [← map_pow,hg,map_one]
  have ha : a = 1 := by
    by_contra hn
    have ho : orderOf a = 5 := orderOf_eq_prime ha7 hn
    have hd : 5 ∣ (Nat.card B).factorial := by
      rw [← Nat.card_perm]
      exact ho ▸ orderOf_dvd_natCard a
    have hh := hd.trans (Nat.factorial_dvd_factorial hsmall)
    norm_num [Nat.factorial] at hh
  exact congrArg (fun p : Equiv.Perm B => (p O).val) ha

end FiveTransitive.NormalizerExteriorOrbitFamilyFive

end CFSG
