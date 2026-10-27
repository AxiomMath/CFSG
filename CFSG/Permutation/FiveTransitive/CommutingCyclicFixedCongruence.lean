module

public import CFSG.Permutation.FiveTransitive.CentralizingSingletonFixed

public section

namespace CFSG

namespace FiveTransitive.CommutingCyclicFixedCongruence

open MulAction

theorem card_modEq
    {X : Type*} [Finite X] {p : ℕ} [Fact p.Prime]
    (P : Subgroup (Equiv.Perm X)) (g r : P)
    (hg : g ^ p = 1) (hcomm : Commute r g) :
    Nat.card (Function.fixedPoints r.val) ≡
      Nat.card {x : Function.fixedPoints g.val // r.val x.val = x.val} [MOD p] := by
  let A := Subgroup.zpowers g
  have hA : IsPGroup p A := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers,pow_one]
    exact orderOf_dvd_of_pow_eq_one hg)
  have hcommA (a : A) : r * a.val = a.val * r := by
    obtain ⟨k,hk⟩ := Subgroup.mem_zpowers_iff.mp a.property
    rw [← hk]
    exact (hcomm.zpow_right k).eq
  have hAeq : fixedPoints A X = Function.fixedPoints g.val :=
    CentralizingSingletonFixed.fixed_zpowers g
  have hh := CentralizingFixedPointCongruence.card_modEq P A hA r hcommA
  rw [hAeq] at hh
  exact hh

end FiveTransitive.CommutingCyclicFixedCongruence

end CFSG
