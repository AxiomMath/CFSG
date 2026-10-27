module

public import CFSG.Permutation.FiveTransitive.Degree60LargeSylowNormalizer
public import CFSG.Permutation.FiveTransitive.Degree60LargePrimeFree

public section

namespace CFSG

namespace FiveTransitive.Degree60LargePrimeConstraints

open MulAction

theorem constraints
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 60)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    {p : ℕ} (hp : p = 59 ∨ p = 29 ∨ p = 19) :
    ∃ d k : ℕ, d ∣ (60 / p).factorial * (p - 1) ∧ (60 % p).factorial ∣ d ∧ k % p = 1 ∧
      d * k * p = Nat.card P := by
  apply Degree60LargeSylowNormalizer.constraints_of_prime_free P hcard h5 hnotAlt hp
  intro s hs
  apply Degree60LargePrimeFree.not_dvd_five_fixer P hcard h5 hnotAlt s hs p
  · rcases hp with rfl | rfl | rfl <;> norm_num
  · rcases hp with rfl | rfl | rfl <;> omega

end FiveTransitive.Degree60LargePrimeConstraints

end CFSG
